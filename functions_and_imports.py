import certifi
from collections import OrderedDict, defaultdict, Counter
import contextlib
import copy
import csv
import datetime
from datetime import datetime
from decimal import Decimal
from difflib import SequenceMatcher, get_close_matches
import fnmatch
import getpass
from getpass import getpass
import glob
import hashlib
import io
from itertools import chain
from IPython import get_ipython
import json
import math
from matplotlib.figure import Figure
import matplotlib.pyplot as plt
import numpy as np
import openpyxl
from openpyxl.styles import PatternFill, Font, Alignment
from openpyxl.utils import get_column_letter, column_index_from_string
from openpyxl.cell import WriteOnlyCell
import os, ssl
import pandas as pd
from pathlib import Path
import platform
import random
import re
from requests.adapters import HTTPAdapter
import requests
import shutil
import signal
import socket
from stat import S_ISREG
import subprocess
import sys
import tempfile
import time
import truststore
import unicodedata
from urllib.parse import quote
import zipfile
cell_durations = {}

################################################################################################################################################################################
#3.00 INPUTS
################################################################################################################################################################################
def round_numeric_columns(frame, decimals=None):
    """Round every numeric column of a results table (an empty table is returned unchanged). decimals defaults to OUTPUT_DECIMALS from the SIT Inputs block (5 when it is not defined)."""
    decimals = globals().get("OUTPUT_DECIMALS", 5) if decimals is None else decimals
    if frame.empty:
        return frame
    numeric_columns = frame.select_dtypes(include="number").columns
    frame[numeric_columns] = frame[numeric_columns].round(decimals)
    return frame
################################################################################################################################################################################
#3.02
################################################################################################################################################################################
RATING_BATTERY_EXCLUDED_CATEGORIES = ("BESS expansion",)   #raw Battery Categories the Ratings Report does not print (future expansion candidates, like the Generator expansion candidates that no Generator group contains); set to () to compare every raw Battery unit
#Ratings Report units that are built from the Generator and Battery sheets of the raw data in addition to the notebook's alias_measures (MW, MBTU). A spec is ACTIVE only when the Blueprint_rat sheet of the
#template has a row with that Alias AND that Class (so Blueprint_rat stays the list of what is validated). Every Timeslice = 'All Periods' / 'Off-Peak' / 'On-Peak' is read from its own raw rows.
#  alias            = the text after the ':' of the printed row label            class = the Blueprint_rat Class (lower case)
#  frame            = which raw sheet the rows come from ('generator' or 'battery')   collections = ((raw Collection, identifier column), ...)
#  column           = the raw measure column                                      factor = raw column -> report unit (GWh -> MWH 1000, $000 -> $ 1000, MWh -> MWh 1)
#  group_class      = the class used to find the raw units (Generator.Fuels rows take the Category of their parent Generator)
#  may_be_missing   = True: when the raw column does not exist or holds no value yet, the kind of row is skipped and said so (it is picked up as soon as the raw data is populated)
#  only_if_in_report= True: used only for a Ratings section that really prints rows with this alias
RATING_NEW_MEASURE_SPECS = [
    {"alias": "Var Cost", "class": "generator", "frame": "generator", "collections": (("Generator", "Child Name"),), "column": "Total System Cost ($000)", "label": "Total System Cost ($000)", "factor": 1000},
    {"alias": "Var O&M", "class": "generator", "frame": "generator", "collections": (("Generator", "Child Name"),), "column": "VO&M Cost ($000)", "label": "VO&M Cost ($000)", "factor": 1000},
    {"alias": "Use", "class": "generator.fuels", "group_class": "generator", "frame": "generator", "collections": (("Generator.Fuels", "Parent Name"),), "column": "Offtake (BBtu)", "label": "Offtake (BBtu)", "factor": 1000, "only_if_in_report": True},
    {"alias": "$", "class": "generator.fuels", "group_class": "generator", "frame": "generator", "collections": (("Generator.Fuels", "Parent Name"),), "column": "Cost ($000)", "label": "Cost ($000)", "factor": 1000, "only_if_in_report": True},
    {"alias": "Chrg", "class": "battery", "frame": "battery", "exclude_categories": RATING_BATTERY_EXCLUDED_CATEGORIES, "collections": (("Battery", "Child Name"),), "column": "Load (GWh)", "label": "Battery Load (GWh)", "factor": 1000, "may_be_missing": True},
    {"alias": "Dchrg", "class": "battery", "frame": "battery", "exclude_categories": RATING_BATTERY_EXCLUDED_CATEGORIES, "collections": (("Battery", "Child Name"),), "column": "Generation (GWh)", "label": "Battery Generation (GWh)", "factor": 1000, "may_be_missing": True},
    {"alias": "Var O&M", "class": "battery", "frame": "battery", "exclude_categories": RATING_BATTERY_EXCLUDED_CATEGORIES, "collections": (("Battery", "Child Name"),), "column": "VO&M Cost ($000)", "label": "VO&M Cost ($000)", "factor": 1000, "may_be_missing": True},
    {"alias": "Storage", "class": "battery", "frame": "battery", "exclude_categories": RATING_BATTERY_EXCLUDED_CATEGORIES, "collections": (("Battery", "Child Name"),), "column": "Energy (MWh)", "label": "Energy (MWh)", "factor": 1, "may_be_missing": True},
]
RATING_PENDING_REPORTED = set()   #"raw data not available yet" lines already printed (each is printed once per run of the block: clear it with RATING_PENDING_REPORTED.clear())
class RatingFrameHolder:
    """Carries the prepared raw Battery frame of ONE Timeslice (and the proof that it holds only that Timeslice) on the .attrs of the raw Generator frame of the same Timeslice, so every function that already receives the Generator frame (build_raw_ratings_tables, build_rating_raw_name_lookup, ...) also reaches the Battery rows without a change of its arguments. It is never copied (pandas copies .attrs when a frame is sliced)."""
    def __init__(self, frame, proven, proof_text):
        self.frame, self.proven, self.proof_text = frame, proven, proof_text
    def __deepcopy__(self, memo):
        return self
    def __copy__(self):
        return self
def rating_measure_factor(measure, default_factor):
    """Raw column -> report unit factor of one kind of Ratings Report row: the 'factor' of the measure when it has one (Storage = MWh x 1), else the factor of the block (RATING_UNIT_FACTOR = 1000)."""
    return measure.get("factor", default_factor)
def rating_measure_source_frame(generator_frame, measure):
    """The raw frame a measure is read from: the Generator frame itself, or the Battery frame carried on its .attrs. Returns frame (None when it is not available) and a problem text ('' when fine)."""
    if measure.get("frame", "generator") != "battery":
        return generator_frame, ""
    holder = generator_frame.attrs.get("rating_battery")
    if holder is None:
        return None, "the raw Battery sheet was not loaded with the Generator frame (load_raw_generator_for_timeslice)"
    if not holder.proven:
        return None, f"Timeslice proof of the raw Battery sheet failed ({holder.proof_text})"
    return holder.frame, ""
def rating_measure_problem(generator_frame, measure):
    """'' when the raw column of a measure exists and holds at least one value in every collection it reads; else the reason (raw column not in the sheet, collection not in the sheet, or the column is still blank). Used to say that the raw data is not available YET."""
    source_frame, problem = rating_measure_source_frame(generator_frame, measure)
    if source_frame is None:
        return problem
    sheet_name = "Battery" if measure.get("frame", "generator") == "battery" else "Generator"
    if measure["column"] not in source_frame.columns:
        return f"the raw {sheet_name} sheet has no column '{measure['column']}'"
    for collection_name, _identifier_column in measure["collections"]:
        collection_rows = source_frame[source_frame["Collection"].astype(str).str.strip() == collection_name]
        if len(collection_rows) == 0:
            return f"the raw {sheet_name} sheet has no '{collection_name}' rows"
        if collection_rows[measure["column"]].notna().sum() == 0:
            return f"the raw {sheet_name} column '{measure['column']}' has no values yet"
    return ""
def rating_definition_active(rating_definition, report_rows):
    """False for a kind of Ratings Report row that is used only when the Ratings section prints rows with its alias (only_if_in_report) and the section prints none."""
    if not rating_definition["measure"].get("only_if_in_report"):
        return True
    alias_lower = rating_definition["alias"].lower()
    return any(report_row["alias"].lower() == alias_lower for report_row in report_rows)
def rating_alias_basis(rating_definitions, alias_text, default_factor):
    """Text of the raw basis of ONE alias, for the section titles: ('Generation (GWh) x 1000', 'Generation (GWh) x 1000'). An alias that has several definitions (Var O&M = Generator + Battery) lists every distinct basis once. Returns label_text, column_text."""
    label_parts, column_parts = [], []
    for definition in rating_definitions:
        if definition["alias"].lower() != alias_text.lower():
            continue
        measure = definition["measure"]
        factor_text = f"{rating_measure_factor(measure, default_factor):g}"
        label_part, column_part = f"{measure['label']} x {factor_text}", f"{measure['column']} x {factor_text}"
        if label_part not in label_parts:
            label_parts.append(label_part)
        if column_part not in column_parts:
            column_parts.append(column_part)
    return " / ".join(label_parts), " / ".join(column_parts)
def read_rating_measure_definitions(template_data_path, alias_measures):
    """Every kind of Ratings Report row to compare, from the template sheet Blueprint_rat (columns Class, Group, Property, Alias): one definition per Blueprint_rat row whose Alias (the text after the ':' of the printed row label, compared ignoring case: 'MW', 'MBTU', 'Var Cost', 'Var O&M', 'Chrg', 'Dchrg', 'Storage') is a key of alias_measures ({alias in lower case: {'collections': ((raw collection, identifier column), ...), 'column': raw measure column, 'label': text}}) or has a spec in RATING_NEW_MEASURE_SPECS (matched on the alias AND the Class of the Blueprint_rat row, so 'Var O&M' of Generator and 'Var O&M' of Battery are two definitions). The (class, group) of the row gives the raw units of the row. When the sheet cannot be read, or has no row for an alias of alias_measures, that alias is added with the default group (generator, thermal) and said so. A Blueprint_rat row that has no raw measure at all is said so and is not compared. Returns a list of {'group_key', 'alias', 'measure': the alias_measures / spec entry, 'source'} (alias_measures first, in their order, then the other rows in the order of Blueprint_rat) and a list of note texts."""
    notes, definitions, found_aliases, found_specs = [], [], set(), set()
    try:
        blueprint_rat = pd.read_excel(template_data_path, sheet_name="Blueprint_rat", dtype=str).fillna("")
        blueprint_rat.columns = [str(c).strip() for c in blueprint_rat.columns]
        for rat_row in blueprint_rat.to_dict("records"):
            alias_text = str(rat_row.get("Alias", "")).strip()
            class_lower, group_lower = str(rat_row.get("Class", "")).strip().lower(), str(rat_row.get("Group", "")).strip().lower()
            if alias_text == "" and class_lower == "":
                continue
            measure = None
            if alias_text.lower() in alias_measures:
                if alias_text.lower() in found_aliases:
                    continue
                found_aliases.add(alias_text.lower())
                measure = alias_measures[alias_text.lower()]
            else:
                for spec in RATING_NEW_MEASURE_SPECS:
                    if spec["alias"].lower() == alias_text.lower() and spec["class"] == class_lower:
                        if (alias_text.lower(), class_lower) not in found_specs:
                            found_specs.add((alias_text.lower(), class_lower))
                            measure = spec
                        break
                if measure is None:
                    if not any(spec["alias"].lower() == alias_text.lower() and spec["class"] == class_lower for spec in RATING_NEW_MEASURE_SPECS):
                        notes.append(f"Blueprint_rat row {rat_row.get('Class', '')} / {rat_row.get('Group', '')} / {rat_row.get('Property', '')} (alias {alias_text}) has no raw measure defined (alias_measures / RATING_NEW_MEASURE_SPECS): it is not compared")
                    continue
            definitions.append({"group_key": (measure.get("group_class", class_lower), group_lower), "alias": alias_text, "measure": measure,
                                "source": f"Blueprint_rat: {rat_row.get('Class', '')} / {rat_row.get('Group', '')} / {rat_row.get('Property', '')} (alias {alias_text})"})
    except Exception as exc:
        notes.append(f"Blueprint_rat could not be read ({type(exc).__name__}: {str(exc)[:80]})")
    for alias_lower, measure in alias_measures.items():
        if alias_lower not in found_aliases:
            notes.append(f"Blueprint_rat has no row with alias '{alias_lower.upper()}': the default group generator / thermal is used")
            definitions.append({"group_key": ("generator", "thermal"), "alias": alias_lower.upper(), "measure": measure, "source": f"default: generator / thermal (alias {alias_lower.upper()})"})
    notebook_aliases = list(alias_measures)
    definitions.sort(key=lambda d: notebook_aliases.index(d["alias"].lower()) if d["alias"].lower() in notebook_aliases else len(notebook_aliases))
    return definitions, notes
def build_rating_raw_rows(generator_frame, month_labels, value_columns, name_map, group_assets, group_key, group_extra_includes, extra_match_case, collections, measure_column, unit_factor, measure=None):
    """The raw side of one kind of Ratings Report row (for example '<name>:MW' = the Generator Generation, '<name>:MBTU' = the generator fuel Offtake) for ONE Timeslice. generator_frame = the raw Generator frame of that Timeslice (all collections). collections = ((collection, identifier column), ...): every listed collection is read and the values of the same unit are ADDED (for example Generator.Fuels + Generator.Start Fuels by Parent Name). A row belongs to the group group_key when the raw Category of its unit is in group_assets (a Generator.* row takes the Category of its parent generator) or it matches the name-level includes of group_extra_includes (a unit of that Category whose name contains one of the strings). Each unit is renamed to the name the report prints (name_map; units that share a printed name are added up), measure_column x unit_factor (1000 = GWh -> MWH, BBtu -> MBTU), a month with no raw value stays blank, Tot-YYYY = the sum of that year's months and Total = the sum of all months. Returns {name key: {'printed': printed name, 'raw_names': sorted raw unit names, 'values': array in the order of value_columns}}. measure = the alias_measures / RATING_NEW_MEASURE_SPECS entry (optional): its 'frame' = 'battery' reads the Battery rows carried on generator_frame.attrs, 'exclude_categories' leaves raw Categories out, and 'may_be_missing' returns {} (instead of failing) while the raw column does not exist or holds no value yet."""
    measure = measure or {}
    if measure.get("may_be_missing") and rating_measure_problem(generator_frame, measure) != "":
        return {}
    generator_frame, frame_problem = rating_measure_source_frame(generator_frame, measure)
    if generator_frame is None:
        raise KeyError(frame_problem)
    if measure_column not in generator_frame.columns:
        raise KeyError(f"the raw {'Battery' if measure.get('frame') == 'battery' else 'Generator'} frame has no column '{measure_column}'")
    excluded_categories = set(str(c).strip().lower() for c in measure.get("exclude_categories", ()))
    unit_category = generator_frame[generator_frame["Collection"].astype(str).str.strip() == "Generator"].drop_duplicates("Child Name").set_index("Child Name")["Category"].astype(str).str.strip().str.lower()
    allowed_categories = group_assets.get(group_key)
    collapse_name = lambda text: re.sub(r"\s+", " ", str(text)).strip()
    parts = []
    for collection_name, identifier_column in collections:
        collection_rows = generator_frame[generator_frame["Collection"].astype(str).str.strip() == collection_name]
        if len(collection_rows) == 0:
            continue
        unit_names = collection_rows[identifier_column].astype(str).map(collapse_name)
        category_key = collection_rows["Category"].astype(str).str.strip().str.lower() if collection_name in ("Generator", "Battery") else collection_rows[identifier_column].map(unit_category).fillna("")
        member = category_key.isin(allowed_categories) if allowed_categories is not None else pd.Series(True, index=collection_rows.index)
        if len(excluded_categories) > 0:
            member = member & ~category_key.isin(excluded_categories)
        for include_category, include_strings in group_extra_includes.get(group_key, []):
            name_hit = pd.Series(False, index=collection_rows.index)
            for include_string in include_strings:
                name_hit |= unit_names.str.contains(re.escape(include_string), case=extra_match_case, na=False)
            member = member | ((category_key == str(include_category).strip().lower()) & name_hit)
        part = pd.DataFrame({"_unit": unit_names[member], "Month": collection_rows.loc[member, "Month"], "_value": collection_rows.loc[member, measure_column]})
        parts.append(part)
    if len(parts) == 0:
        return {}
    members = pd.concat(parts, ignore_index=True)
    members["_printed"] = members["_unit"].map(lambda raw_name: collapse_name(name_map.get(normalize_text(raw_name), raw_name)))
    members["_key"] = members["_printed"].map(rating_name_key)
    members["_label"] = rating_month_labels(members["Month"])
    members = members[members["_label"].isin(set(month_labels))]
    monthly = members.groupby(["_key", "_label"])["_value"].sum(min_count=1).unstack("_label").reindex(columns=month_labels) * unit_factor
    raw_rows = {}
    for name_key, month_values in monthly.iterrows():
        month_array = month_values.to_numpy(dtype=float)
        values = np.full(len(value_columns), np.nan)
        for column_position, column_name in enumerate(value_columns):
            if column_name.startswith("Tot-"):
                year_positions = [i for i, m in enumerate(month_labels) if m.endswith(column_name[4:])]
                year_values = month_array[year_positions] if len(year_positions) > 0 else np.array([])
                values[column_position] = float(np.nansum(year_values)) if (len(year_values) > 0 and not np.isnan(year_values).all()) else np.nan
            elif column_name == "Total":
                values[column_position] = float(np.nansum(month_array)) if not np.isnan(month_array).all() else np.nan
            elif column_name in month_labels:
                values[column_position] = month_array[month_labels.index(column_name)]
        rows_of_unit = members[members["_key"] == name_key]
        raw_rows[name_key] = {"printed": rows_of_unit["_printed"].iloc[0], "raw_names": sorted(set(rows_of_unit["_unit"])), "values": values}
    return raw_rows
def count_matching_rating_rows(rating_rows, raw_rows, alias, rel_tol, abs_tol, dropped_name_keys):
    """How many Ratings Report rows with the label alias have a raw row (same name key) whose values all agree (numpy isclose with rel_tol / abs_tol, a blank counts as 0). Used to check that the raw collections chosen for a kind of row are the ones the report is built from. Returns matching_rows, compared_rows."""
    matching_rows = compared_rows = 0
    seen_keys = set()
    for rating_row in rating_rows:
        if rating_row["alias"].lower() != alias.lower() or rating_row["name_key"] in dropped_name_keys or rating_row["name_key"] in seen_keys:
            continue
        seen_keys.add(rating_row["name_key"])
        compared_rows += 1
        raw_row = raw_rows.get(rating_row["name_key"])
        if raw_row is not None and bool(np.isclose(np.nan_to_num(rating_row["values"]), np.nan_to_num(raw_row["values"]), rtol=rel_tol, atol=abs_tol).all()):
            matching_rows += 1
    return matching_rows, compared_rows
def rating_name_key(text):
    """Comparison key of a name: extra spaces collapsed, trimmed, lower case ('FUT CT A                       :MW' and 'Fut Ct A :mw' are the same key)."""
    return re.sub(r"\s+", " ", str(text)).strip().lower()
def rating_timeslice_key(text, section_aliases):
    """Canonical key of a Ratings Report section title or of a raw Timeslice value, so the two can be paired: text in brackets and a day range such as 'Mon-Sun' are ignored, everything except letters and digits is dropped, then section_aliases is applied ('All Periods' -> 'atc', 'Off-Peak' -> 'offpeak', 'On-Peak' -> 'onpeak' with the aliases of the block)."""
    day_token = r"(?:mon|tue|tues|wed|weds|thu|thur|thurs|fri|sat|sun|monday|tuesday|wednesday|thursday|friday|saturday|sunday)"
    cleaned = re.sub(r"\([^)]*\)", "", str(text).lower())
    cleaned = re.sub(rf"\b{day_token}\s*-\s*{day_token}\b", "", cleaned)
    cleaned = re.sub(r"[^a-z0-9]+", "", cleaned)
    return section_aliases.get(cleaned, cleaned)
def rating_value_header_key(header):
    """One spelling for a value column header so the same month compares equal whatever the year is written like: 'Jan-26', 'Jan-2026', 'January 2026', '2026-01' -> 'Jan-2026'; 'Tot-2026', 'Tot-26', 'Total 2026', '2026 Total' -> 'Tot-2026'; 'Total' / 'Grand Total' -> 'Total'; any other text is returned unchanged (stripped)."""
    text = str(header).strip()
    low = re.sub(r"\s+", " ", text.lower().replace("_", " "))
    month_names = ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
    found = re.match(r"^(" + "|".join(month_names) + r")[a-z]*[-\s/'.]*(\d{2}|\d{4})$", low)
    if found:
        year_number = int(found.group(2))
        return f"{found.group(1).title()}-{year_number + 2000 if year_number < 100 else year_number}"
    found = re.match(r"^(\d{4})[-/](\d{1,2})(?:[-/]\d{1,2})?(?:\s.*)?$", low)
    if found and 1 <= int(found.group(2)) <= 12:
        return f"{month_names[int(found.group(2)) - 1].title()}-{found.group(1)}"
    found = re.match(r"^(?:tot|total)[-\s:_]*(\d{2}|\d{4})$", low) or re.match(r"^(\d{2}|\d{4})[-\s:_]*(?:tot|total)$", low)
    if found:
        year_number = int(found.group(1))
        return f"Tot-{year_number + 2000 if year_number < 100 else year_number}"
    return "Total" if low in ("total", "grand total", "tot") else text
def parse_rating_report_rows(report_rows, value_columns, section_aliases):
    """Parse the rows of the Ratings Report CSV (PLEXOS_rr_rows) on their own, before any filter of the block: a row with exactly one filled cell is a section title (its canonical key is rating_timeslice_key), the next row with a blank first cell is that section's header row, every other row with a label is a data row. Value columns are matched by their canonical header (rating_value_header_key), so a 2-digit year ('Jan-26') or an empty trailing cell does not matter; a column with a blank header is ignored. Returns {section key: {'title', 'rows': [{'label' (spaces collapsed), 'label_key', 'name' (text before the last ':'), 'name_key', 'alias' (text after the last ':', for example MW or MBTU), 'values' (array in the order of value_columns, NaN where the section has no such column)}], 'missing_columns': value columns the section header does not have, 'titles_seen': how many times the section title was printed}}."""
    sections, current, header_positions = {}, None, None
    for report_row in report_rows:
        cells = [str(c).strip() for c in report_row]
        filled = [c for c in cells if c != ""]
        if len(filled) == 0:
            continue
        if len(filled) == 1 and cells[0] != "":
            current = rating_timeslice_key(cells[0], section_aliases)
            if current in sections:
                sections[current]["titles_seen"] += 1
            else:
                sections[current] = {"title": cells[0], "rows": [], "missing_columns": [], "titles_seen": 1}
            header_positions = None
            continue
        if current is None:
            continue
        if cells[0] == "":
            header_positions = {}
            for position, header in enumerate(cells[1:], start=1):
                if header != "":
                    header_positions.setdefault(rating_value_header_key(header), position)
            sections[current]["missing_columns"] = [c for c in value_columns if c not in header_positions]
            continue
        if header_positions is None:
            continue
        label = re.sub(r"\s+", " ", cells[0]).strip()
        name_part, alias = (cells[0].rsplit(":", 1) if ":" in cells[0] else (cells[0], ""))
        values = np.full(len(value_columns), np.nan)
        for column_position, column_name in enumerate(value_columns):
            cell_position = header_positions.get(column_name)
            if cell_position is not None and cell_position < len(cells):
                converted = pd.to_numeric(cells[cell_position], errors="coerce")
                values[column_position] = float(converted) if pd.notna(converted) else np.nan
        sections[current]["rows"].append({"label": label, "label_key": rating_name_key(cells[0]), "name": re.sub(r"\s+", " ", name_part).strip(), "name_key": rating_name_key(name_part), "alias": alias.strip(), "values": values})
    return sections
def read_rating_generation_definitions(template_data_path, default_group=("generator", "thermal"), default_alias="MW"):
    """The Ratings Report rows that are Generation, from the template sheet Blueprint_rat (columns Class, Group, Property, Alias): every row whose Property is 'Generation' gives (class, group) = the raw units of the row and Alias = the text after the ':' of the printed row label (for example 'MW'). The default (Generator / Thermal / MW) is used, and said so, when the sheet or a Generation row cannot be read. Returns a list of {'group_key': (class, group) in lower case, 'alias': text, 'source': text} and a note text ('' when the sheet was read)."""
    note = ""
    try:
        blueprint_rat = pd.read_excel(template_data_path, sheet_name="Blueprint_rat", dtype=str).fillna("")
        blueprint_rat.columns = [str(c).strip() for c in blueprint_rat.columns]
        definitions = []
        for rat_row in blueprint_rat.to_dict("records"):
            if str(rat_row.get("Property", "")).strip().lower() == "generation":
                definitions.append({"group_key": (str(rat_row.get("Class", "")).strip().lower(), str(rat_row.get("Group", "")).strip().lower()), "alias": str(rat_row.get("Alias", "")).strip(),
                                    "source": f"Blueprint_rat: {rat_row.get('Class', '')} / {rat_row.get('Group', '')} / Generation (alias {rat_row.get('Alias', '')})"})
        if len(definitions) > 0:
            return definitions, note
        note = "Blueprint_rat has no Generation row"
    except Exception as exc:
        note = f"Blueprint_rat could not be read ({type(exc).__name__}: {str(exc)[:80]})"
    return [{"group_key": default_group, "alias": default_alias, "source": f"default: {default_group[0]} / {default_group[1]} / Generation (alias {default_alias})"}], note
def list_raw_timeslice_values(raw_cache, raw_data_path, sheet_name="Generator"):
    """Every Timeslice value of the raw Generator sheet (the unfiltered sheet kept in the session cache SIT_RAW_CACHE, else read from the workbook), in the order they first appear; the column is found whatever its spelling. Returns the values and the column name ('' when the sheet has no Timeslice column)."""
    frame = raw_cache.get("df_gen") if isinstance(raw_cache, dict) else None
    if frame is None:
        frame = pd.read_excel(raw_data_path, sheet_name=sheet_name)
    timeslice_column = next((c for c in frame.columns if re.sub(r"[^a-z]", "", str(c).lower()) == "timeslice"), None)
    if timeslice_column is None:
        return [], ""
    return [str(v).strip() for v in frame[timeslice_column].dropna().unique()], str(timeslice_column)
def load_raw_generator_for_timeslice(raw_data_path, timeslice, excel_serial_min, excel_serial_max):
    """The raw Generator frame of ONE Timeslice, prepared exactly like the frames of the Standard Report comparison (load_raw_frames_cached: Timeslice filter + Month labels), plus a proof that it holds only that Timeslice. Only the lines of load_raw_frames_cached that contain WARNING are printed. Returns the frame, a True / False for the proof and a text. NOTE: load_raw_frames_cached keeps ONE prepared copy in the session cache, so call it again with the Standard Report Timeslice afterwards (the block does) to leave the cache as it was."""
    import io, contextlib
    captured = io.StringIO()
    with contextlib.redirect_stdout(captured):
        loaded_frames = load_raw_frames_cached(raw_data_path, timeslice, excel_serial_min, excel_serial_max)
    for captured_line in captured.getvalue().splitlines():
        if "WARNING" in captured_line:
            print(captured_line)
    generator_frame = loaded_frames[2]
    #the Battery rows of the same Timeslice (Ratings Chrg / Dchrg / Var O&M / Storage rows) travel on the .attrs of the Generator frame; the frame itself, its rows and the proof below are unchanged
    battery_frame = loaded_frames[0]
    battery_timeslice_column = next((c for c in battery_frame.columns if re.sub(r"[^a-z]", "", str(c).lower()) == "timeslice"), None)
    if battery_timeslice_column is None:
        battery_proven, battery_proof = False, "the raw Battery frame has no Timeslice column, so the Timeslice cannot be proven"
    else:
        battery_found = sorted(set(battery_frame[battery_timeslice_column].astype(str).str.strip()))
        battery_proven = battery_found == [str(timeslice).strip()]
        battery_proof = f"only '{timeslice}' rows ({len(battery_frame)} raw Battery row(s))" if battery_proven else f"Timeslice values found: {battery_found} (expected only '{timeslice}')"
    generator_frame.attrs["rating_battery"] = RatingFrameHolder(battery_frame, battery_proven, battery_proof)
    timeslice_column = next((c for c in generator_frame.columns if re.sub(r"[^a-z]", "", str(c).lower()) == "timeslice"), None)
    if timeslice_column is None:
        return generator_frame, False, "the raw Generator frame has no Timeslice column, so the Timeslice cannot be proven"
    found_values = sorted(set(generator_frame[timeslice_column].astype(str).str.strip()))
    proven = found_values == [str(timeslice).strip()]
    return generator_frame, proven, (f"only '{timeslice}' rows ({len(generator_frame)} raw Generator row(s))" if proven else f"Timeslice values found: {found_values} (expected only '{timeslice}')")
def rating_month_labels(month_column):
    """Month labels ('Jan-2026') of a raw Month column that holds dates or already holds labels / date text."""
    if pd.api.types.is_datetime64_any_dtype(month_column):
        return month_column.dt.strftime("%b-%Y")
    as_text = month_column.astype(str).str.strip()
    already_labels = as_text.str.match(r"^(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)-\d{4}$")
    converted = pd.to_datetime(as_text.where(~already_labels), errors="coerce").dt.strftime("%b-%Y")
    return as_text.where(already_labels, converted)
def build_rating_raw_generation_rows(generator_frame, month_labels, value_columns, name_map, group_assets, group_key, group_extra_includes, extra_match_case, generation_column, unit_factor):
    """The raw side of one Ratings Report Generation row set: the Generator rows of ONE Timeslice whose unit belongs to the group group_key (raw Category in group_assets, or the name-level includes of group_extra_includes: a unit of that Category whose Child Name contains one of the strings), each unit renamed to the name the report prints (name_map; units that share a printed name are added up), generation_column ('Generation (GWh)') multiplied by unit_factor (1000 = GWh -> MWH, the unit of Standard Report Table 2), a month that has no raw value stays blank, Tot-YYYY = the sum of that year's months and Total = the sum of all months (generation is energy, so the report sums it). Returns {name key: {'printed': printed name, 'raw_names': sorted raw Child Names, 'values': array in the order of value_columns}}."""
    if generation_column not in generator_frame.columns:
        raise KeyError(f"the raw Generator frame has no column '{generation_column}'")
    unit_rows = generator_frame[generator_frame["Collection"].astype(str).str.strip() == "Generator"]
    category_key = unit_rows["Category"].astype(str).str.strip().str.lower()
    allowed_categories = group_assets.get(group_key)
    member = category_key.isin(allowed_categories) if allowed_categories is not None else pd.Series(True, index=unit_rows.index)
    child_collapsed = unit_rows["Child Name"].astype(str).str.replace(r"\s+", " ", regex=True).str.strip()
    for include_category, include_strings in group_extra_includes.get(group_key, []):
        name_hit = pd.Series(False, index=unit_rows.index)
        for include_string in include_strings:
            name_hit |= child_collapsed.str.contains(re.escape(include_string), case=extra_match_case, na=False)
        member = member | ((category_key == str(include_category).strip().lower()) & name_hit)
    members = unit_rows[member].copy()
    members["_printed"] = child_collapsed[member].map(lambda raw_name: re.sub(r"\s+", " ", str(name_map.get(normalize_text(raw_name), raw_name))).strip())
    members["_key"] = members["_printed"].map(rating_name_key)
    members["_label"] = rating_month_labels(members["Month"])
    members = members[members["_label"].isin(set(month_labels))]
    monthly = members.groupby(["_key", "_label"])[generation_column].sum(min_count=1).unstack("_label").reindex(columns=month_labels) * unit_factor
    raw_rows = {}
    for name_key, month_values in monthly.iterrows():
        month_array = month_values.to_numpy(dtype=float)
        values = np.full(len(value_columns), np.nan)
        for column_position, column_name in enumerate(value_columns):
            if column_name.startswith("Tot-"):
                year_positions = [i for i, m in enumerate(month_labels) if m.endswith(column_name[4:])]
                year_values = month_array[year_positions] if len(year_positions) > 0 else np.array([])
                values[column_position] = float(np.nansum(year_values)) if (len(year_values) > 0 and not np.isnan(year_values).all()) else np.nan
            elif column_name == "Total":
                values[column_position] = float(np.nansum(month_array)) if not np.isnan(month_array).all() else np.nan
            elif column_name in month_labels:
                values[column_position] = month_array[month_labels.index(column_name)]
        rows_of_unit = members[members["_key"] == name_key]
        raw_rows[name_key] = {"printed": rows_of_unit["_printed"].iloc[0], "raw_names": sorted(set(rows_of_unit["Child Name"].astype(str).str.replace(r"\s+", " ", regex=True).str.strip())), "values": values}
    return raw_rows
def compare_rating_generation_section(report_name, section_key, section_title, rating_rows, raw_rows, alias, value_columns, meta_columns, rel_tol, abs_tol, not_present, names_max_shown, dropped_name_keys):
    """Row by row comparison of ONE Ratings Report section (one Timeslice) with the raw rows of the same Timeslice, in the layout of the Standard Report row-by-row comparison: for every pair the PLEXOS row directly above the Raw Data row, Pair Status MATCH / DIFFERS (n of N columns) / Only in PLEXOS / Only in Raw Data, a value matching when numpy isclose(PLEXOS, raw, rtol=rel_tol, atol=abs_tol) holds (a blank counts as 0). Only the rows of the section whose label alias is alias are compared; rows whose name key is in dropped_name_keys (removed from the Ratings Report by an earlier filter of the block, for example the retired-resource filter) are left out on both sides and listed. Returns frame (meta_columns + value_columns), diff_matrix (bool, one line per frame row), summary (dict), excluded (list of dicts)."""
    format_names = lambda names: " + ".join(names[:names_max_shown]) + (f" (+{len(names) - names_max_shown} more)" if len(names) > names_max_shown else "")
    blank_values = np.full(len(value_columns), np.nan)
    pair_records, diff_lines, excluded = [], [], []
    counts = {"MATCH": 0, "DIFFERS": 0, "Only in PLEXOS": 0, "Only in Raw Data": 0}
    largest_difference, matched_raw_keys, occurrence_seen = 0.0, set(), {}
    def add_pair(px_title, raw_title, names_text, status, px_values, raw_values, diff_vector):
        for source, title, values in (("PLEXOS", px_title, px_values), ("Raw Data", raw_title, raw_values)):
            record = {"Report": report_name, "Table Number": section_key, "Table Title": section_title, "Source": source, "Row Title": title, "Raw Data Name(s)": names_text, "Pair Status": status}
            record.update(dict(zip(value_columns, values)))
            pair_records.append(record)
            diff_lines.append(diff_vector)
    for rating_row in rating_rows:
        if rating_row["alias"].lower() != alias.lower():
            continue
        if rating_row["name_key"] in dropped_name_keys:
            excluded.append({"Report": report_name, "Table Number": section_key, "Side": "PLEXOS", "Row Title": rating_row["label"], "Raw Data Name(s)": "", "Reason": "Row removed from the Ratings Report by an earlier filter of this block (retired-resource / structural-row filter); left out on both sides"})
            continue
        occurrence_seen[rating_row["name_key"]] = occurrence_seen.get(rating_row["name_key"], 0) + 1
        raw_row = raw_rows.get(rating_row["name_key"]) if occurrence_seen[rating_row["name_key"]] == 1 else None
        if raw_row is None:
            counts["Only in PLEXOS"] += 1
            add_pair(rating_row["label"], not_present, "", "Only in PLEXOS", rating_row["values"], blank_values, np.zeros(len(value_columns), dtype=bool))
            continue
        matched_raw_keys.add(rating_row["name_key"])
        px_clean, raw_clean = np.nan_to_num(rating_row["values"]), np.nan_to_num(raw_row["values"])
        close = np.isclose(px_clean, raw_clean, rtol=rel_tol, atol=abs_tol)
        differing = int((~close).sum())
        largest_difference = max(largest_difference, float(np.max(np.abs(px_clean - raw_clean))) if len(px_clean) > 0 else 0.0)
        counts["MATCH" if differing == 0 else "DIFFERS"] += 1
        add_pair(rating_row["label"], f"{raw_row['printed']}:{rating_row['alias']}", format_names(raw_row["raw_names"]), "MATCH" if differing == 0 else f"DIFFERS ({differing} of {len(value_columns)} columns)",
                 rating_row["values"], raw_row["values"], ~close)
    for name_key in sorted(k for k in raw_rows if k not in matched_raw_keys):
        raw_row = raw_rows[name_key]
        if name_key in dropped_name_keys:
            excluded.append({"Report": report_name, "Table Number": section_key, "Side": "Raw Data", "Row Title": f"{raw_row['printed']}:{alias}", "Raw Data Name(s)": format_names(raw_row["raw_names"]), "Reason": "Its Ratings Report row was removed by an earlier filter of this block (retired-resource / structural-row filter); left out on both sides"})
            continue
        counts["Only in Raw Data"] += 1
        add_pair(not_present, f"{raw_row['printed']}:{alias}", format_names(raw_row["raw_names"]), "Only in Raw Data", blank_values, raw_row["values"], np.zeros(len(value_columns), dtype=bool))
    frame = pd.DataFrame(pair_records, columns=meta_columns + list(value_columns))
    diff_matrix = np.array(diff_lines, dtype=bool) if len(diff_lines) > 0 else np.zeros((0, len(value_columns)), dtype=bool)
    summary = {"Report": report_name, "Table Number": section_key, "Table Title": section_title, "Row Pairs": len(pair_records) // 2, "MATCH": counts["MATCH"], "DIFFERS": counts["DIFFERS"], "Only in PLEXOS": counts["Only in PLEXOS"],
               "Only in Raw Data": counts["Only in Raw Data"], "Excluded (removed earlier)": len(excluded), "Largest Absolute Difference": round(largest_difference, 6)}
    return frame, diff_matrix, summary, excluded
def write_rating_generation_workbook(workbook_path, summary_frame, section_tables, excluded_frame, not_compared_frame, meta_columns, value_columns, meta_widths, fill_head, fill_band, fill_diff):
    """One workbook for the Ratings Report generation comparison: a Summary sheet, one 'Rat <section key>' sheet per Timeslice (PLEXOS row directly above the Raw Data row, pairs shaded alternately, every cell that differs shaded red, header row and the first 7 columns frozen), a sheet of the rows left out and a sheet of the Ratings Report rows that were not compared. section_tables = {sheet name: {'frame': DataFrame, 'diff_matrix': bool array}}. Returns the path."""
    import openpyxl
    from openpyxl.styles import Font
    from openpyxl.utils import get_column_letter
    workbook = openpyxl.Workbook()
    def write_plain_sheet(sheet, frame):
        sheet.append([str(c) for c in frame.columns])
        for cell in sheet[1]:
            cell.font, cell.fill = Font(bold=True), fill_head
        for record in frame.itertuples(index=False):
            sheet.append([None if (isinstance(v, float) and np.isnan(v)) else (v.item() if isinstance(v, np.generic) else v) for v in record])
        for column_position, column_name in enumerate(frame.columns, start=1):
            longest = max([len(str(column_name))] + [len(str(v)) for v in frame[column_name].head(200)])
            sheet.column_dimensions[get_column_letter(column_position)].width = min(max(10, longest + 2), 60)
        sheet.freeze_panes = "A2"
    summary_sheet = workbook.active
    summary_sheet.title = "Summary"
    write_plain_sheet(summary_sheet, summary_frame)
    for sheet_name, table in section_tables.items():
        sheet = workbook.create_sheet(sheet_name[:31])
        frame, diff_matrix = table["frame"], table["diff_matrix"]
        sheet.append(list(frame.columns))
        for cell in sheet[1]:
            cell.font, cell.fill = Font(bold=True), fill_head
        for row_position, record in enumerate(frame.itertuples(index=False)):
            sheet.append([None if (isinstance(v, float) and np.isnan(v)) else v for v in record])
            sheet_row = row_position + 2
            for column_position in range(1, len(frame.columns) + 1):
                cell = sheet.cell(row=sheet_row, column=column_position)
                if (row_position // 2) % 2 == 1:
                    cell.fill = fill_band
                if column_position > len(meta_columns):
                    cell.number_format = "#,##0.00"
                    if diff_matrix[row_position, column_position - len(meta_columns) - 1]:
                        cell.fill = fill_diff
        for column_position, width in enumerate(meta_widths, start=1):
            sheet.column_dimensions[get_column_letter(column_position)].width = width
        for column_position in range(len(meta_columns) + 1, len(frame.columns) + 1):
            sheet.column_dimensions[get_column_letter(column_position)].width = 14
        sheet.freeze_panes = sheet.cell(row=2, column=len(meta_columns) + 1)
    write_plain_sheet(workbook.create_sheet("Excluded"), excluded_frame)
    write_plain_sheet(workbook.create_sheet("Not compared"), not_compared_frame)
    workbook.save(workbook_path)
    return workbook_path
def find_excluded_raw_names(exclude_fragments_by_table, name_map, raw_frames):
    """Raw units (Generator Child Name, Battery Child Name, Region Child Name) whose PRINTED name (the raw name through name_map, the name the Standard Report prints) contains one of the fragments of exclude_fragments_by_table ({table: [fragment, ...]}, the same rule the row-by-row comparison uses: case and extra spaces are ignored). Prints one line per fragment, and a WARNING for a fragment that matches no raw unit (the exclusion would then do nothing). Returns {fragment (lower case, single spaces): sorted list of raw names}."""
    collapse = lambda text: re.sub(r"\s+", " ", str(text)).strip()
    unit_names = set()
    for frame_key, frame in raw_frames.items():
        unit_rows = frame[frame["Collection"].astype(str).str.fullmatch("Generator|Battery|Region")] if "Collection" in frame.columns else frame
        unit_names |= set(collapse(n) for n in unit_rows["Child Name"].dropna().unique())
    fragments = sorted(set(collapse(f).lower() for table_fragments in exclude_fragments_by_table.values() for f in table_fragments))
    excluded_by_fragment = {}
    for fragment in fragments:
        excluded_by_fragment[fragment] = sorted(n for n in unit_names if fragment in collapse(map_printed_name(n, name_map)).lower())
        if excluded_by_fragment[fragment]:
            print(f"  Raw unit(s) excluded by the rule '{fragment}': {excluded_by_fragment[fragment]} (printed as: {sorted(set(collapse(map_printed_name(n, name_map)) for n in excluded_by_fragment[fragment]))})")
        else:
            print(f"  WARNING: the exclusion rule '{fragment}' matches no raw unit through the name map, so it excludes nothing")
    return excluded_by_fragment
def rebuild_tables_without_excluded_names(table_keys, excluded_names_by_fragment, extracted_parts, blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                                          class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """A raw unit that the PLEXOS report does not print (the exclusion list, found with find_excluded_raw_names) must not be added into a SUMMARY table either: Table 1 (System Summary) sums every unit of a group, so Novo BioPower (printed as Biomass Snowflake), which sits in the Renewable group through the name-level include, was added to 'Wind/Solar Generation (MWH)' and 'Wind/Solar Total Costs ($)'. The listed tables (table_keys) are extracted AGAIN from copies of the raw frames without the excluded units (the frames in raw_frames are not changed, so the units still appear, and are still excluded, in the tables where the report is compared row by row) and replace the earlier result. extracted_parts = (extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys), changed in place. A table is replaced only when its rows and month columns are identical to the earlier ones (only values and the raw-name lists change); otherwise it is left as it was and a PROBLEM line says so. Prints the rows whose values changed. Returns a DataFrame (one row per changed table row; one per table that was not replaced) for the CSV report."""
    import io, contextlib
    collapse = lambda text: re.sub(r"\s+", " ", str(text)).strip()
    report_columns = ["Table", "Row", "Excluded Raw Name(s) Removed", "Months Changed", "Sum Of Monthly Values Before", "Sum Of Monthly Values After", "Removed", "Status"]
    excluded_names = sorted(set(n for names in excluded_names_by_fragment.values() for n in names))
    if len(excluded_names) == 0:
        print("  Excluded raw units: none found, so no summary table is rebuilt")
        return pd.DataFrame(columns=report_columns)
    excluded_keys = set(collapse(n) for n in excluded_names)
    filtered_frames = {}
    for frame_key, frame in raw_frames.items():
        child_hit = frame["Child Name"].map(collapse).isin(excluded_keys)
        parent_hit = frame["Parent Name"].map(collapse).isin(excluded_keys) if "Parent Name" in frame.columns else child_hit & False
        fuel_rows = frame["Collection"].astype(str).str.startswith("Generator.")
        filtered_frames[frame_key] = frame[~((child_hit & ~fuel_rows) | (parent_hit & fuel_rows))]
    removed_rows = {k: len(raw_frames[k]) - len(filtered_frames[k]) for k in raw_frames}
    print(f"  Rebuilding summary table(s) {list(table_keys)} without {excluded_names}: raw rows left out {removed_rows}")
    old_tables = {t: extracted_parts[0][t].copy() for t in table_keys if t in extracted_parts[0]}
    old_names = {t: dict(extracted_parts[2].get(t, {})) for t in old_tables}
    with contextlib.redirect_stdout(io.StringIO()):
        rebuilt = extract_blueprint_sections(blueprint, filtered_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, list(table_keys), class_to_raw,
                                             property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case)
    report_rows = []
    for table_key in table_keys:
        if table_key not in old_tables or table_key not in rebuilt[0]:
            print(f"  PROBLEM: table {table_key} is not in the extraction, so it was not rebuilt")
            report_rows.append({"Table": table_key, "Row": "(whole table)", "Excluded Raw Name(s) Removed": "", "Months Changed": 0, "Sum Of Monthly Values Before": np.nan, "Sum Of Monthly Values After": np.nan, "Removed": np.nan, "Status": "NOT REPLACED: table not in the extraction"})
            continue
        old_frame, new_frame = old_tables[table_key], rebuilt[0][table_key]
        if list(old_frame.index) != list(new_frame.index) or list(old_frame.columns) != list(new_frame.columns):
            print(f"  PROBLEM: table {table_key} has different rows or month columns without the excluded units, so it was NOT replaced (the earlier values are kept)")
            report_rows.append({"Table": table_key, "Row": "(whole table)", "Excluded Raw Name(s) Removed": "", "Months Changed": 0, "Sum Of Monthly Values Before": np.nan, "Sum Of Monthly Values After": np.nan, "Removed": np.nan, "Status": "NOT REPLACED: rows or month columns differ"})
            continue
        for part_position in range(7):
            if table_key in rebuilt[part_position]:
                extracted_parts[part_position][table_key] = rebuilt[part_position][table_key]
        old_values, new_values = old_frame.to_numpy(dtype=float), new_frame.to_numpy(dtype=float)
        same_cell = np.isclose(np.nan_to_num(old_values), np.nan_to_num(new_values), rtol=0.0, atol=1e-9)
        for row_position in np.flatnonzero(~same_cell.all(axis=1)):
            row_key = old_frame.index[row_position]
            old_listed = set(collapse(n) for n in str(old_names[table_key].get(row_key, "")).split(" + "))
            new_listed = set(collapse(n) for n in str(extracted_parts[2][table_key].get(row_key, "")).split(" + "))
            removed_here = sorted(n for n in excluded_names if collapse(n) in old_listed and collapse(n) not in new_listed)
            before, after = float(np.nansum(old_values[row_position])), float(np.nansum(new_values[row_position]))
            report_rows.append({"Table": table_key, "Row": str(extracted_parts[1][table_key].get(row_key, row_key)).strip(), "Excluded Raw Name(s) Removed": " + ".join(removed_here), "Months Changed": int((~same_cell[row_position]).sum()),
                                "Sum Of Monthly Values Before": before, "Sum Of Monthly Values After": after, "Removed": before - after, "Status": "REPLACED"})
    report = pd.DataFrame(report_rows, columns=report_columns)
    for _, report_row in report[report["Status"] == "REPLACED"].iterrows():
        print(f"    Table {report_row['Table']} '{report_row['Row']}': {report_row['Excluded Raw Name(s) Removed']} removed from {int(report_row['Months Changed'])} month(s); sum of the monthly values {report_row['Sum Of Monthly Values Before']:,.1f} -> {report_row['Sum Of Monthly Values After']:,.1f}")
    if report[report["Status"] == "REPLACED"].empty and report[report["Status"] != "REPLACED"].empty:
        print("    No value in the rebuilt table(s) changed: the excluded units were not part of any summary row")
    return report
def add_start_fuel_blueprint_rows(blueprint, raw_frames, contract_factor, source_class="fuel", start_class="fuel.start", start_collection="Generator.Start Fuels"):
    """Contract sections (Contract Fuel Use / Contract Cost): the report adds the fuel burned to START the units to the fuel burned to run them (for example EP Cont Gas = Generator.Fuels + Generator.Start Fuels of AZGAS EP PHX/Yuma, and FC Start Gas = Generator.Start Fuels of FC45_Coal_Gas only), but Blueprint_std only has one row per measure for the Generator.Fuels collection. When the raw Generator sheet holds a start_collection, every Blueprint row of class source_class is copied with the class start_class, so the same section is also built from the start-fuel rows (add CLASS_TO_RAW[start_class] and PROPERTY_TO_RAW_COLUMN for the collection next to it). Prints one line, plus a warning for every start-fuel name that has no Contract_factors entry (factor 1.0 is then used). Returns blueprint (a new table when rows were added), rows_added."""
    df_gen = raw_frames["df_gen"]
    start_names = sorted(df_gen.loc[df_gen["Collection"] == start_collection, "Child Name"].dropna().astype(str).unique()) if "Collection" in df_gen.columns else []
    if len(start_names) == 0:
        print(f"  Start fuels: the raw Generator sheet has no '{start_collection}' rows; the contract sections are built from Generator.Fuels only")
        return blueprint, 0
    start_rows = blueprint[blueprint["Class"].astype(str).str.strip().str.lower() == source_class].copy()
    if len(start_rows) == 0:
        print(f"  Start fuels: '{start_collection}' is in the raw data but Blueprint_std has no class '{source_class}' row to copy; nothing added")
        return blueprint, 0
    start_rows["Class"] = start_class
    print(f"  Start fuels: {len(start_rows)} Blueprint_std row(s) of class '{source_class}' copied as class '{start_class}' so the contract sections also read '{start_collection}' ({len(start_names)} start-fuel name(s): {start_names})")
    without_factor = [n for n in start_names if normalize_text(n) not in contract_factor]
    if without_factor:
        print(f"  WARNING: start-fuel name(s) with no Contract_factors entry (factor 1.0 is used, the section 23 values for them are not converted): {without_factor}")
    return pd.concat([blueprint, start_rows], ignore_index=True), len(start_rows)
def relabel_section_unit_suffix(section_key, unit_suffix, extracted, extracted_display, extracted_names, extracted_idonly):
    """A raw name has ONE printed name in the maptable_ sheets / NAME_MAP_OVERRIDES, but the Contract Cost section prints the same row labels as Contract Fuel Use with the unit in brackets replaced ('FC45 Cont   (Tons  )' -> 'FC45 Cont   ($)', 'EP Cont Gas (mmBtu )' -> 'EP Cont Gas ($)'; a label without brackets such as 'Fut Tl Coal' is unchanged). This renames the rows of ONE already extracted section accordingly (extracted, extracted_display, extracted_names and extracted_idonly are updated in place; rows that end up with the same label are added up). Run it right after extract_blueprint_sections. Prints one line. Returns the number of rows relabeled."""
    if section_key not in extracted:
        print(f"  Section {section_key}: not extracted from the raw data, so its row labels are not changed")
        return 0
    def relabel(shown_label):
        return re.sub(r"\([^)]*\)\s*$", unit_suffix, str(shown_label))
    old_to_new = {key: normalize_text(relabel(shown)) for key, shown in extracted_display[section_key].items()}
    renamed_frame = extracted[section_key].rename(index=old_to_new)
    if renamed_frame.index.has_duplicates:
        renamed_frame = renamed_frame.groupby(level=0, sort=False).sum(min_count=1)
    extracted[section_key] = renamed_frame
    extracted_display[section_key] = {old_to_new[key]: relabel(shown) for key, shown in extracted_display[section_key].items()}
    extracted_names[section_key] = {old_to_new.get(key, key): names for key, names in extracted_names[section_key].items()}
    extracted_idonly[section_key] = {old_to_new.get(key, key) for key in extracted_idonly[section_key]}
    relabeled_rows = sum(1 for key, new_key in old_to_new.items() if key != new_key)
    print(f"  Section {section_key}: {relabeled_rows} of {len(old_to_new)} row label(s) relabeled with the unit '{unit_suffix}' (the same labels as the contract fuel section, unit in brackets replaced)")
    return relabeled_rows
def build_table3_fuel_use_values(plexos_rows, table_present, value_columns):
    """Table 3 (Thermal Unit Fuel Use): rebuild each generator's PLEXOS series as (Primary) + (Secondary) + (Topping) straight from the Standard Report rows (Startup is not part of the raw Offtake). Header spellings (Jan-2026, Jan-26, 2026-01, Tot-2026, 2026 Total, Total) are matched to value_columns, the row label is the first filled cell left of the first value column, sub-rows are recognised by their text, and a generator printed WITHOUT any sub-row takes its own row values (it used to become all zeros). Same return layout as build_table3_primary_values: {generator: [one array per occurrence]}. Unreadable cells, unmatched header columns and own-row fallbacks are printed."""
    month_names = ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
    month_text_pattern = re.compile(r"^(" + "|".join(month_names) + r")[a-z]*[-\s/'.]*(\d{2}|\d{4})$")
    iso_date_pattern = re.compile(r"^(\d{4})[-/](\d{1,2})(?:[-/]\d{1,2})?(?:\s.*)?$")
    total_year_patterns = (re.compile(r"^(?:tot|total)[-\s:_]*(\d{4})$"), re.compile(r"^(\d{4})[-\s:_]*(?:tot|total)$"))
    section_header_re, section_3_re = re.compile(r"^\(\s*\d+[a-zA-Z]?\s*\)"), re.compile(r"^\(\s*3\s*\)")
    value_set = set(value_columns)
    def header_name(cell_text):
        low = re.sub(r"\s+", " ", str(cell_text).strip().lower().replace("_", " "))
        found = month_text_pattern.match(low)
        if found:
            return f"{found.group(1).title()}-{int(found.group(2)) + (2000 if len(found.group(2)) == 2 else 0)}"
        found = iso_date_pattern.match(low)
        if found and 1 <= int(found.group(2)) <= 12:
            return f"{month_names[int(found.group(2)) - 1].title()}-{found.group(1)}"
        for total_pattern in total_year_patterns:
            found = total_pattern.match(low)
            if found:
                return f"Tot-{found.group(1)}"
        return "Total" if low in ("total", "grand total", "tot") else str(cell_text).strip()
    def read_values(raw_row, header_positions, counters):
        values = np.zeros(len(value_columns))
        for column_index, cell_position in enumerate(header_positions):
            if cell_position is not None and cell_position < len(raw_row):
                cell_clean = str(raw_row[cell_position]).replace(",", "").replace("$", "").replace("%", "").strip()
                if cell_clean != "":
                    try:
                        values[column_index] = float(cell_clean)
                    except ValueError:
                        counters["unreadable"] += 1
        return values
    records, counters, missing_header_columns = {}, {"unreadable": 0}, None
    in_section_3, header_positions, first_value_position, current_entry = False, None, 1, None
    for report_row in plexos_rows if table_present else []:
        stripped = [str(c).strip() for c in report_row]
        non_blank = [c for c in stripped if c]
        if not non_blank:
            continue
        row_text = " ".join(non_blank)
        if section_header_re.match(row_text):
            in_section_3, header_positions, current_entry = bool(section_3_re.match(row_text)), None, None
            continue
        if not in_section_3:
            continue
        if header_positions is None:
            positions = {}
            for cell_index, cell_text in enumerate(stripped):
                cell_name = header_name(cell_text) if cell_text != "" else ""
                if cell_name in value_set and cell_name not in positions:
                    positions[cell_name] = cell_index
            if positions:
                header_positions = [positions.get(c) for c in value_columns]
                first_value_position = max(min(p for p in header_positions if p is not None), 1)
                if missing_header_columns is None:
                    missing_header_columns = [c for c, p in zip(value_columns, header_positions) if p is None]
            continue
        label_cells = [c for c in stripped[:first_value_position] if c]
        label = normalize_text(label_cells[0]) if label_cells else ""
        if label == "":
            continue
        if label == "total":
            current_entry = None
            continue
        if label.startswith("("):
            if current_entry is None:
                continue
            kind = re.sub(r"[^a-z]", "", label)
            if "startup" in kind or kind == "start":
                current_entry["has_sub"] = True
            elif "primary" in kind or "secondary" in kind or "topping" in kind:
                current_entry["has_sub"] = True
                current_entry["sub"] = current_entry["sub"] + read_values(report_row, header_positions, counters)
        else:
            current_entry = {"own": read_values(report_row, header_positions, counters), "sub": np.zeros(len(value_columns)), "has_sub": False}
            records.setdefault(label, []).append(current_entry)
    table3_px_values = {name: [e["sub"] if e["has_sub"] else e["own"] for e in entries] for name, entries in records.items()}
    own_row_count = sum(1 for entries in records.values() for e in entries if not e["has_sub"])
    print(f"Table 3 PLEXOS rebuild (Primary + Secondary + Topping) prepared for {len(table3_px_values)} generator(s)")
    if counters["unreadable"] > 0:
        print(f"  WARNING: {counters['unreadable']} Table 3 cell(s) could not be read as numbers and were counted as 0.0")
    if missing_header_columns:
        print(f"  WARNING Table 3: the CSV header has no column matching {len(missing_header_columns)} of {len(value_columns)} value column(s) (they are read as 0): {missing_header_columns[:12]}")
    if own_row_count > 0:
        print(f"  Table 3: {own_row_count} generator occurrence(s) are printed without (Primary) / (Secondary) / (Startup) / (Topping) rows; their own row values are used")
    if table_present and len(table3_px_values) == 0:
        print("  WARNING: no Table 3 generator rows were read straight from the Standard Report; Table 3 falls back to the ordinary row totals (which include start-up fuel)")
    return table3_px_values
def canonical_header(header):
    """Turn many header spellings into the layout names: Jan-2026, Tot-2026, Total."""
    text = str(header).strip()
    low = re.sub(r"\s+", " ", text.lower().replace("_", " "))
    found = month_text_re.match(low)
    if found:
        year_number = int(found.group(2))
        if year_number < 100:
            year_number += 2000
        return f"{found.group(1).title()}-{year_number}"
    found = iso_date_re.match(low)
    if found:
        month_number = int(found.group(2))
        if 1 <= month_number <= 12:
            return f"{MONTH_ABBR[month_number]}-{found.group(1)}"
    found = total_year_a_re.match(low)
    if found is None:
        found = total_year_b_re.match(low)
    if found:
        return f"Tot-{found.group(1)}"
    if low in ("total", "grand total", "tot"):
        return "Total"
    return text
def prepare_compare_frame(frame, expected_value_columns, label):
    """Works on a COPY: normalizes header names, makes duplicate headers unique, assigns the expected headers by position when the column count is exact."""
    frame = frame.copy()
    notes = []
    original_headers = [str(c) for c in frame.columns]
    renamed = [original_headers[0]] + [canonical_header(c) for c in original_headers[1:]]
    seen_headers = {}
    unique_headers = []
    for header in renamed:
        if header in seen_headers:
            seen_headers[header] += 1
            unique_headers.append(f"{header}.{seen_headers[header]}")
        else:
            seen_headers[header] = 0
            unique_headers.append(header)
    if unique_headers != original_headers:
        notes.append("header names were normalized / made unique")
    frame.columns = unique_headers
    headers_found = set(frame.columns[1:])
    missing_headers = [c for c in expected_value_columns if c not in headers_found]
    if len(missing_headers) > 0 and frame.shape[1] == len(expected_value_columns) + 1:
        frame.columns = [frame.columns[0]] + list(expected_value_columns)
        notes.append(f"{len(missing_headers)} header(s) still did not match, so the expected headers were assigned by position")
        missing_headers = []
    if len(missing_headers) > 0:
        notes.append(f"{len(missing_headers)} expected month / total column(s) NOT FOUND (column count {frame.shape[1]}, expected {len(expected_value_columns) + 1}): their values will be blank")
        month_coverage_rows.append({"Table Side": label, "Columns In Table": frame.shape[1], "Expected Columns": len(expected_value_columns) + 1,
                                    "Missing Count": len(missing_headers), "Missing Columns": ", ".join(missing_headers),
                                    "Original Headers (first 12)": ", ".join(original_headers[:12])})
    if len(notes) > 0:
        print(f"  NOTE {label}: " + "; ".join(notes))
    return frame
def canonical_header(header):
    text = str(header).strip()
    low = re.sub(r"\s+", " ", text.lower().replace("_", " "))
    found = month_text_re.match(low)
    if found:
        year_number = int(found.group(2))
        if year_number < 100:
            year_number += 2000
        return f"{found.group(1).title()}-{year_number}"
    found = iso_date_re.match(low)
    if found:
        month_number = int(found.group(2))
        if 1 <= month_number <= 12:
            return f"{MONTH_ABBR[month_number]}-{found.group(1)}"
    found = total_year_a_re.match(low)
    if found is None:
        found = total_year_b_re.match(low)
    if found:
        return f"Tot-{found.group(1)}"
    if low in ("total", "grand total", "tot"):
        return "Total"
    return text
def prepare_compare_frame(frame, expected_value_columns, label):
    frame = frame.copy()
    notes = []
    original_headers = [str(c) for c in frame.columns]
    renamed = [original_headers[0]] + [canonical_header(c) for c in original_headers[1:]]
    seen_headers = {}
    unique_headers = []
    for header in renamed:
        if header in seen_headers:
            seen_headers[header] += 1
            unique_headers.append(f"{header}.{seen_headers[header]}")
        else:
            seen_headers[header] = 0
            unique_headers.append(header)
    if unique_headers != original_headers:
        notes.append("header names were normalized / made unique")
    frame.columns = unique_headers
    headers_found = set(frame.columns[1:])
    missing_headers = [c for c in expected_value_columns if c not in headers_found]
    if len(missing_headers) > 0 and frame.shape[1] == len(expected_value_columns) + 1:
        frame.columns = [frame.columns[0]] + list(expected_value_columns)
        notes.append(f"{len(missing_headers)} header(s) still did not match, so the expected headers were assigned by position")
        missing_headers = []
    if len(missing_headers) > 0:
        notes.append(f"{len(missing_headers)} expected month / total column(s) NOT FOUND (column count {frame.shape[1]}, expected {len(expected_value_columns) + 1}): their values will be blank")
        month_coverage_rows.append({"Table Side": label, "Columns In Table": frame.shape[1], "Expected Columns": len(expected_value_columns) + 1,
                                    "Missing Count": len(missing_headers), "Missing Columns": ", ".join(missing_headers),
                                    "Original Headers (first 12)": ", ".join(original_headers[:12])})
    if len(notes) > 0:
        print(f"  NOTE {label}: " + "; ".join(notes))
    return frame
def make_report_headers_unique(reports):
    tables_changed = 0
    for rep_name, rep_data in reports.items():
        for tables_key in ("PLEXOS_tables", "Raw_tables"):
            table_dict = rep_data.get(tables_key) or {}
            for tbl_number, tbl in table_dict.items():
                frm = tbl["data"] if (isinstance(tbl, dict) and "data" in tbl) else tbl
                if not hasattr(frm, "columns"):
                    continue
                if not frm.columns.duplicated().any():
                    continue
                seen_headers = {}
                unique_headers = []
                for header in frm.columns:
                    if header in seen_headers:
                        seen_headers[header] += 1
                        unique_headers.append(f"{header}.{seen_headers[header]}")
                    else:
                        seen_headers[header] = 0
                        unique_headers.append(header)
                frm.columns = unique_headers
                tables_changed += 1
    return tables_changed
def read_value_matrix(frame, value_columns):
    """The listed columns of a section table as a float matrix (rows x columns). Numeric columns are taken as they are (no change to the values); text columns have "," "$" "%" removed first; an unreadable or missing cell is NaN."""
    selected = frame.reindex(columns=value_columns)
    return selected.apply(lambda column: pd.to_numeric(column.astype(str).str.replace(",", "", regex=False).str.replace("$", "", regex=False).str.replace("%", "", regex=False), errors="coerce") if column.dtype == object else pd.to_numeric(column, errors="coerce")).to_numpy(dtype=float)
def drop_raw_only_exclusions(ordered_keys, px_pos, raw_pos, raw_labels, raw_name_lookup, exclude_fragments, report_name, table_number, table_title):
    """Step A: raw-only rows that do not belong in the table (their title or raw name contains an exclusion fragment) are dropped from the comparison and listed instead of being reported as missing from PLEXOS. Returns kept_keys, excluded_records."""
    kept_keys, excluded_records = [], []
    for key in ordered_keys:
        if key not in px_pos and len(exclude_fragments) > 0:
            raw_title_check = raw_labels[raw_pos[key]]
            raw_names_check = raw_name_lookup.get(key.rsplit("||", 1)[0], "")
            haystack = re.sub(r"\s+", " ", raw_title_check + " " + raw_names_check).lower()
            matched_fragments = [fragment for fragment in exclude_fragments if fragment in haystack]
            if len(matched_fragments) > 0:
                excluded_records.append({"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Row Title": raw_title_check, "Raw Data Name(s)": raw_names_check,
                                         "Matched Exclusion Rule": ", ".join(matched_fragments), "Reason": "Raw-only row that does not belong in this table (not printed in the PLEXOS report)"})
                continue
        kept_keys.append(key)
    return kept_keys, excluded_records
def build_pair_matrices(kept_keys, px_pos, raw_pos, px_matrix, raw_matrix, n_value_columns, table3_values):
    """Step B: line the PLEXOS and Raw Data values up pair by pair (one row per pair, NaN where a side has no row). table3_values (None except for Standard Table 3) replaces the PLEXOS values of Table 3 with Primary + Secondary + Topping. Returns px_index, raw_index, has_px, has_raw, pair_px, pair_raw."""
    n_pairs = len(kept_keys)
    px_index = np.array([px_pos.get(k, -1) for k in kept_keys], dtype=int)
    raw_index = np.array([raw_pos.get(k, -1) for k in kept_keys], dtype=int)
    has_px, has_raw = px_index >= 0, raw_index >= 0
    pair_px, pair_raw = np.full((n_pairs, n_value_columns), np.nan), np.full((n_pairs, n_value_columns), np.nan)
    if has_px.any():
        pair_px[has_px] = px_matrix[px_index[has_px]]
    if has_raw.any():
        pair_raw[has_raw] = raw_matrix[raw_index[has_raw]]
    if table3_values is not None:
        for pair_number in np.flatnonzero(has_px).tolist():
            name_only, occurrence = kept_keys[pair_number].rsplit("||", 1)
            if name_only in table3_values and int(occurrence) < len(table3_values[name_only]):
                pair_px[pair_number] = table3_values[name_only][int(occurrence)]
    return px_index, raw_index, has_px, has_raw, pair_px, pair_raw
def label_pairs(kept_keys, px_index, raw_index, px_labels, raw_labels, raw_name_lookup, raw_identifier_only, diff_counts, n_value_columns, not_present, raw_names_max_shown):
    """Step C2: the row titles, the raw workbook name(s) (the first few plus a count) and the Pair Status (MATCH / DIFFERS / Only in PLEXOS / Only in Raw Data / Raw identifier only) of every pair. Returns px_titles, raw_titles, raw_originals, statuses, counts."""
    px_titles, raw_titles, raw_originals, statuses = [], [], [], []
    counts = {"MATCH": 0, "DIFFERS": 0, "Only in PLEXOS": 0, "Only in Raw Data": 0, "Raw identifier only": 0}
    for pair_number, key in enumerate(kept_keys):
        pi, ri = int(px_index[pair_number]), int(raw_index[pair_number])
        px_titles.append(px_labels[pi] if pi >= 0 else not_present)
        raw_titles.append(raw_labels[ri] if ri >= 0 else not_present)
        raw_original = ""
        if ri >= 0:
            raw_names_text = raw_name_lookup.get(key.rsplit("||", 1)[0], "")
            raw_name_list = [n for n in raw_names_text.split(" + ") if n]
            raw_original = (" + ".join(raw_name_list[:raw_names_max_shown]) + f" (+{len(raw_name_list) - raw_names_max_shown} more)") if len(raw_name_list) > raw_names_max_shown else raw_names_text
        raw_originals.append(raw_original)
        if pi >= 0 and ri >= 0:
            if raw_identifier_only[pair_number]:
                status = "Raw identifier only (no raw measure)"
            elif diff_counts[pair_number] == 0:
                status = "MATCH"
            else:
                status = f"DIFFERS ({int(diff_counts[pair_number])} of {n_value_columns} columns)"
        else:
            status = "Only in PLEXOS" if pi >= 0 else "Only in Raw Data"
        counts[status if status in counts else ("DIFFERS" if status.startswith("DIFFERS") else "Raw identifier only")] += 1
        statuses.append(status)
    return px_titles, raw_titles, raw_originals, statuses, counts
def build_table_comparison(report_name, table_number, table_title, raw_df, px_df, value_columns, raw_name_lookup, rel_tol, abs_tol, exclude_fragments, table3_values, meta_columns, not_present, raw_names_max_shown):
    """The row-by-row comparison of ONE section: pair the rows (normalized title, occurrence by occurrence; PLEXOS report order first, raw-only rows last), drop the raw-only rows that do not belong in the table, compare every pair at once (NaN counts as 0, relative rel_tol, absolute abs_tol) and put every PLEXOS row directly above its Raw Data row. Returns frame, diff_matrix, summary_row, excluded_records, only_px_titles (the rows printed by PLEXOS only)."""
    n_value_columns = len(value_columns)
    raw_labels = raw_df.iloc[:, 0].astype(str).str.strip().reset_index(drop=True)
    px_labels = px_df.iloc[:, 0].astype(str).str.strip().reset_index(drop=True)
    raw_matrix, px_matrix = read_value_matrix(raw_df, value_columns), read_value_matrix(px_df, value_columns)
    raw_norm, raw_key = build_occurrence_keys(raw_labels)
    px_norm, px_key = build_occurrence_keys(px_labels)
    raw_labels, px_labels = raw_labels.tolist(), px_labels.tolist()
    raw_pos, px_pos = {k: i for i, k in enumerate(raw_key)}, {k: i for i, k in enumerate(px_key)}
    ordered_keys = px_key + [k for k in raw_key if k not in px_pos]
    kept_keys, excluded_records = drop_raw_only_exclusions(ordered_keys, px_pos, raw_pos, raw_labels, raw_name_lookup, exclude_fragments, report_name, table_number, table_title)
    n_pairs = len(kept_keys)
    px_index, raw_index, has_px, has_raw, pair_px, pair_raw = build_pair_matrices(kept_keys, px_pos, raw_pos, px_matrix, raw_matrix, n_value_columns, table3_values)
    raw_identifier_only = np.isnan(pair_raw).all(axis=1)
    close = np.isclose(np.nan_to_num(pair_px), np.nan_to_num(pair_raw), rtol=rel_tol, atol=abs_tol)
    diff_matrix = (~close) & ((has_px & has_raw) & ~raw_identifier_only)[:, None]
    px_titles, raw_titles, raw_originals, statuses, counts = label_pairs(kept_keys, px_index, raw_index, px_labels, raw_labels, raw_name_lookup, raw_identifier_only, diff_matrix.sum(axis=1), n_value_columns, not_present, raw_names_max_shown)
    row_titles = [None] * (2 * n_pairs)
    row_titles[0::2], row_titles[1::2] = px_titles, raw_titles
    meta_frame = pd.DataFrame({"Report": [report_name] * (2 * n_pairs), "Table Number": [table_number] * (2 * n_pairs), "Table Title": [table_title] * (2 * n_pairs), "Source": ["PLEXOS", "Raw Data"] * n_pairs,
                               "Row Title": row_titles, "Raw Data Name(s)": [v for v in raw_originals for _ in (0, 1)], "Pair Status": [v for v in statuses for _ in (0, 1)]}, columns=meta_columns)
    interleaved = np.empty((2 * n_pairs, n_value_columns))
    interleaved[0::2], interleaved[1::2] = pair_px, pair_raw
    frame = pd.concat([meta_frame, pd.DataFrame(interleaved, columns=value_columns)], axis=1)
    summary_row = {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Row Pairs": len(ordered_keys) - len(excluded_records), "MATCH": counts["MATCH"], "DIFFERS": counts["DIFFERS"],
                   "Only in PLEXOS": counts["Only in PLEXOS"], "Only in Raw Data": counts["Only in Raw Data"], "Raw identifier only": counts["Raw identifier only"], "Excluded (not in table)": len(excluded_records)}
    only_px_titles = [title for title, status in zip(px_titles, statuses) if status == "Only in PLEXOS"]
    return frame, diff_matrix, summary_row, excluded_records, only_px_titles
def write_row_compare_workbook(workbook_path, row_compare_summary, comparison_tables, excluded_rows, meta_columns, value_columns, meta_widths, excluded_widths, fill_head, fill_band, fill_diff):
    """Write the Excel workbook: a Summary sheet, one sheet per table (PLEXOS row directly above its Raw Data row, banded pairs, differing cells shaded red, frozen header and meta columns) and an 'Excluded' sheet. Uses xlsxwriter when it is installed (much faster on large sheets), else openpyxl (same cell values, number formats and shading). Returns the engine used."""
    import copy
    try:
        import xlsxwriter
        excel_engine = "xlsxwriter"
    except ImportError:
        excel_engine = "openpyxl"
    excel_options = {"engine_kwargs": {"options": {"nan_inf_to_errors": True}}} if excel_engine == "xlsxwriter" else {}
    print(f"  Excel engine: {excel_engine}")
    first_value_column, last_column = len(meta_columns) + 1, len(meta_columns) + len(value_columns)
    with pd.ExcelWriter(workbook_path, engine=excel_engine, **excel_options) as writer:
        row_compare_summary.to_excel(writer, sheet_name="Summary", index=False)
        if excel_engine == "xlsxwriter":
            workbook = writer.book
            head_format = workbook.add_format({"bold": True, "bg_color": "#D9E1F2", "border": 1, "align": "center", "valign": "top"})
            band_format = workbook.add_format({"bg_color": "#F2F2F2"})
            num_format = workbook.add_format({"num_format": "#,##0.00"})
            diff_format = workbook.add_format({"num_format": "#,##0.00", "bg_color": "#FFC7CE"})
            for sheet_name, table in comparison_tables.items():
                frame, diff_matrix = table["frame"], table["diff_matrix"]
                worksheet = workbook.add_worksheet(sheet_name)
                for column_number, column_name in enumerate(frame.columns):
                    worksheet.write_string(0, column_number, str(column_name), head_format)
                worksheet.freeze_panes(1, first_value_column - 1)
                for column_number, width in enumerate(meta_widths):
                    worksheet.set_column(column_number, column_number, width)
                meta_rows = frame[meta_columns].to_numpy().tolist()
                value_rows = frame[value_columns].to_numpy(dtype=float).tolist()
                for row_offset in range(len(frame)):
                    sheet_row, pair_index = row_offset + 1, row_offset // 2
                    meta_format = band_format if pair_index % 2 == 1 else None
                    for column_number, meta_value in enumerate(meta_rows[row_offset]):
                        worksheet.write_string(sheet_row, column_number, str(meta_value), meta_format)
                    differing = set(np.flatnonzero(diff_matrix[pair_index]).tolist())
                    for position, value in enumerate(value_rows[row_offset]):
                        cell_format = diff_format if position in differing else num_format
                        if value != value:
                            worksheet.write_blank(sheet_row, first_value_column - 1 + position, None, cell_format)
                        else:
                            worksheet.write_number(sheet_row, first_value_column - 1 + position, value, cell_format)
            if len(excluded_rows) > 0:
                excluded_frame = pd.DataFrame(excluded_rows)
                excluded_frame.to_excel(writer, sheet_name="Excluded", index=False)
                excluded_sheet = writer.sheets["Excluded"]
                for column_number, column_name in enumerate(excluded_frame.columns):
                    excluded_sheet.write_string(0, column_number, str(column_name), head_format)
                for column_number, width in enumerate(excluded_widths):
                    excluded_sheet.set_column(column_number, column_number, width)
            summary_sheet = writer.sheets["Summary"]
            for column_number, column_name in enumerate(row_compare_summary.columns):
                summary_sheet.write_string(0, column_number, str(column_name), head_format)
            summary_sheet.set_column(2, 2, 42)
        else:
            style_cache = {}
            for sheet_name, table in comparison_tables.items():
                frame, diff_matrix = table["frame"], table["diff_matrix"]
                frame.to_excel(writer, sheet_name=sheet_name, index=False)
                worksheet = writer.sheets[sheet_name]
                apply_openpyxl_header_style(worksheet=worksheet, header_fill=fill_head)
                worksheet.freeze_panes = worksheet.cell(row=2, column=first_value_column)
                set_openpyxl_column_widths(worksheet=worksheet, widths=meta_widths, start_column=1)
                if len(frame) > 0:
                    for row_offset, row_cells in enumerate(worksheet.iter_rows(min_row=2, max_row=1 + len(frame), min_col=1, max_col=last_column)):
                        pair_index = row_offset // 2
                        if pair_index % 2 == 1:
                            for cell in row_cells[:first_value_column - 1]:
                                if "band" in style_cache:
                                    cell._style = copy.copy(style_cache["band"])
                                else:
                                    cell.fill = fill_band
                                    style_cache["band"] = copy.copy(cell._style)
                        differing = set(np.flatnonzero(diff_matrix[pair_index]).tolist())
                        for position, cell in enumerate(row_cells[first_value_column - 1:]):
                            look = "num_diff" if position in differing else "num"
                            if look in style_cache:
                                cell._style = copy.copy(style_cache[look])
                            else:
                                cell.number_format = "#,##0.00"
                                if look == "num_diff":
                                    cell.fill = fill_diff
                                style_cache[look] = copy.copy(cell._style)
            if len(excluded_rows) > 0:
                pd.DataFrame(excluded_rows).to_excel(writer, sheet_name="Excluded", index=False)
                excluded_sheet = writer.sheets["Excluded"]
                apply_openpyxl_header_style(worksheet=excluded_sheet, header_fill=fill_head)
                set_openpyxl_column_widths(worksheet=excluded_sheet, widths=excluded_widths, start_column=1)
            summary_sheet = writer.sheets["Summary"]
            apply_openpyxl_header_style(worksheet=summary_sheet, header_fill=fill_head)
            summary_sheet.column_dimensions["C"].width = 42
    return excel_engine
def build_raw_unit_catalog(raw_frames):
    """Every raw unit (Generator / Region / Battery) by normalized name: {name: (raw sheet, raw Category)}. Generator.Fuels rows are the fuels of the generators, so they are not listed."""
    sheet_names = {"df_gen": "Generator", "df_reg": "Region", "df_bat": "Battery"}
    catalog = {}
    for frame_key, frame in raw_frames.items():
        units = frame[frame["Collection"] != "Generator.Fuels"].drop_duplicates("Child Name")
        for unit_name, unit_category in zip(units["Child Name"], units["Category"]):
            catalog.setdefault(normalize_text(unit_name), (sheet_names.get(frame_key, frame_key), str(unit_category).strip()))
    return catalog
def find_raw_units_missing_from_sections(only_px_records, name_map, unit_catalog):
    """For every row that only PLEXOS prints: is the unit in the raw data after all (under its own name or a name the maptable_ maps to the printed title)? Such a unit was left out of the raw section by a group / category definition (or the retired list), it is not missing from the raw data. Returns a table with the raw name(s) and raw Category (empty when every PLEXOS-only row really has no raw unit)."""
    printed_to_raw = {}
    for raw_key, printed_name in name_map.items():
        printed_to_raw.setdefault(normalize_text(printed_name), []).append(raw_key)
    found_rows = []
    for report_name, table_number, row_title in only_px_records:
        title_key = normalize_text(row_title)
        raw_names = list(dict.fromkeys([k for k in printed_to_raw.get(title_key, []) if k in unit_catalog] + ([title_key] if title_key in unit_catalog else [])))
        if raw_names:
            found_rows.append({"Report": report_name, "Table Number": table_number, "PLEXOS Row Title": row_title, "Raw Name(s) In The Raw Data": " + ".join(raw_names),
                               "Raw Sheet": ", ".join(sorted({unit_catalog[n][0] for n in raw_names})), "Raw Category": ", ".join(sorted({unit_catalog[n][1] for n in raw_names})),
                               "Likely Cause": "The raw data HAS this unit but it is not in the raw section: its raw Category is not in the group this section uses (USER_GROUP_CATEGORIES / GROUP_EXTRA_INCLUDES in PlexOS-3.02) or it was removed as retired"})
    return pd.DataFrame(found_rows, columns=["Report", "Table Number", "PLEXOS Row Title", "Raw Name(s) In The Raw Data", "Raw Sheet", "Raw Category", "Likely Cause"])
def require_global_names(required_names, block_name, run_first="the SIT Inputs block and the PlexOS-3.02 script"):
    """Confirm that variables required from earlier SIT blocks exist (run_first names what to run if they are missing)."""
    missing_names = [name for name in required_names if name not in globals()]
    if missing_names:
        raise NameError(f"{block_name} needs {missing_names}. Run {run_first} first (same session).")
def prompt_missing_inputs(input_prompts):
    """For each (variable_name, prompt_text): reuse the variable if an earlier test defined it, otherwise ask once (Enter = empty)."""
    for variable_name, prompt_text in input_prompts:
        if variable_name in globals():
            print(f"  {variable_name}: already entered earlier -> reusing '{globals()[variable_name]}'")
        else:
            globals()[variable_name] = clean_user_path(prompt_text)
def validate_and_report_inputs(required_inputs, sit_step, tc_name):
    """Validate the input files, print the results table and PASS line; on a missing file print the Step 1 FAIL lines and re-raise."""
    try:
        file_validation_results = validate_input_files(required_inputs=required_inputs, sit_step=sit_step)
    except FileNotFoundError:
        print("Step 1 Status: FAIL")
        print(f"FAILED: {tc_name}")
        raise
    print(file_validation_results.to_string(index=False))
    print(f"{sit_step} input files: PASS - all required files were found.")
    return file_validation_results
def build_raw_column_layout(gen_month_dt):
    """Normalized raw layout from the Generator month datetimes. Returns month_labels, raw_years, raw_columns, expected_monthly_columns."""
    month_labels = gen_month_dt.dropna().drop_duplicates().sort_values().dt.strftime("%b-%Y").tolist()
    raw_years = sorted(set(int(m[-4:]) for m in month_labels))
    raw_columns = [""]
    for yr in raw_years:
        raw_columns.extend(m for m in month_labels if m.endswith(str(yr)))
        raw_columns.append(f"Tot-{yr}")
    raw_columns.append("Total")
    expected_monthly_columns = len(month_labels) + len(raw_years) + 1
    print(f"  Normalized raw layout: {len(month_labels)} months + {len(raw_years)} Tot-YYYY + 1 Total = {expected_monthly_columns} columns")
    return month_labels, raw_years, raw_columns, expected_monthly_columns
def resolve_group_assets(group_assets, user_group_categories, category_aliases, raw_categories_present, group_extra_includes):
    """Apply the SIT group definitions (by raw Category) over the template Groups sheet, compare them and print each group.
    Updates group_assets in place. Returns group_check_df."""
    group_check_rows = []
    sheet_group_assets = dict(group_assets)
    for gkey in sorted(set(sheet_group_assets) | set(user_group_categories)):
        if gkey in user_group_categories:
            cat_list = user_group_categories[gkey]
            resolved = set(category_aliases.get(c.strip().lower(), c.strip().lower()) for c in cat_list)
            sheet_set = sheet_group_assets.get(gkey, "missing")
            if sheet_set == "missing":
                agreement = "Group is not on the template Groups sheet"
            elif sheet_set is None:
                agreement = "Template Groups sheet says 'all' (no filter)"
            else:
                only_defined = sorted((resolved & raw_categories_present) - (sheet_set & raw_categories_present))
                only_sheet = sorted((sheet_set & raw_categories_present) - (resolved & raw_categories_present))
                agreement = "Agrees with the template Groups sheet" if not only_defined and not only_sheet else (
                    f"Differs from the template Groups sheet (defined only here: {only_defined}; on the sheet only: {only_sheet})")
            group_assets[gkey] = resolved
            source = "SIT definition"
            listed = ", ".join(cat_list)
        else:
            resolved = sheet_group_assets[gkey]
            agreement = "Taken from the template Groups sheet"
            source = "Template Groups sheet"
            listed = "all" if resolved is None else ", ".join(sorted(resolved))
        in_raw = set(raw_categories_present) if resolved is None else (resolved & raw_categories_present)
        not_in_raw = set() if resolved is None else (resolved - raw_categories_present)
        extra_text = "; ".join(f"{rc} units containing {' / '.join(strs)}" for rc, strs in group_extra_includes.get(gkey, []))
        group_check_rows.append({"Class": gkey[0], "Group": gkey[1], "Source": source, "Defined Categories": listed,
                                 "Resolved Raw Categories": ", ".join(sorted(in_raw)), "Name-Level Includes": extra_text,
                                 "Defined But Not In Raw Data": ", ".join(sorted(not_in_raw)), "Template Groups Sheet": agreement})
        print(f"  Group {gkey[1].title()} [{source}] = {', '.join(sorted(in_raw))}"
              f"{' (no raw category: ' + ', '.join(sorted(not_in_raw)) + ')' if not_in_raw else ''}: {agreement}")
        if extra_text:
            print(f"      plus name-level includes: {extra_text}")
    return pd.DataFrame(group_check_rows)
def resolve_battery_columns(property_to_raw_column, battery_column_aliases, df_bat):
    """Pick the first alias found on the raw Battery sheet for each Battery property (updates and returns property_to_raw_column)."""
    for battery_property, battery_aliases in battery_column_aliases.items():
        battery_found = [c for c in battery_aliases if c in df_bat.columns]
        if battery_found:
            property_to_raw_column[("df_bat", "Battery")][battery_property] = battery_found[0]
        else:
            print(f"  WARNING: the raw Battery sheet has none of the columns {battery_aliases} for Battery {battery_property}: those Blueprint rows will be listed as 'raw column not in the workbook'")
    battery_columns = property_to_raw_column[("df_bat", "Battery")]
    print(f"  Battery raw columns used: Generation = '{battery_columns['Generation']}', Load = '{battery_columns['Load']}'")
    return property_to_raw_column
def extract_blueprint_sections(blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                               in_scope_tables, class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables,
                               section_special_factor, extra_include_match_case):
    """Rebuild the in-scope Standard Report sections from the raw frames, driven by Blueprint_std (one pass over the Blueprint rows).
    Returns (extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys,
    cov_df, table_order, out_of_scope_tables, blueprint_titles)."""
    extracted, extracted_display, extracted_names, extracted_raw_ids = {}, {}, {}, {}
    extracted_idonly, extracted_rate, extracted_derived_keys = {}, {}, {}
    coverage_rows, table_order, blueprint_titles = [], [], {}
    out_of_scope_tables, seen_specs = set(), set()
    df_gen = raw_frames["df_gen"]
    parent_cat = df_gen[df_gen["Collection"] == "Generator"].drop_duplicates("Child Name").set_index("Child Name")["Category"].astype(str).str.strip().str.lower()
    raw_parts = {}
    for part_fkey, part_frame in raw_frames.items():
        for part_coll, part_rows in part_frame.groupby("Collection", sort=False):
            raw_parts[(part_fkey, part_coll)] = part_rows
    part_key_cache, group_mask_cache, report_name_cache = {}, {}, {}
    for brow in blueprint.to_dict("records"):
        header = brow["Header"]
        tmatch = re.match(r"^\(\s*(\w+)\s*\)", header)
        tkey = tmatch.group(1).lower() if tmatch else header.lower()
        if tkey not in in_scope_tables:
            out_of_scope_tables.add(tkey)
            continue
        if tkey not in table_order:
            table_order.append(tkey)
            blueprint_titles[tkey] = map_printed_name(header, name_map)
        cls_in, grp_in, prop_in, pattern = brow["Class"], brow["Group"], brow["Property"], brow["Pattern"].lower()
        cls_l, grp_l = cls_in.lower(), grp_in.lower()
        unit_bp = brow["Unit"]
        sign = float(brow["Sign"]) if brow["Sign"] != "" else 1.0
        use_mean = brow["Rate"].strip().lower() in ("true", "1", "yes")
        cov = {"Table": tkey, "Header": header, "Class": cls_in, "Group": grp_in, "Property": prop_in, "Pattern": pattern,
               "Blueprint Unit": unit_bp, "Sign": sign, "Raw DataFrame": "", "Raw Collection": "", "Raw Column": "",
               "Raw Unit": "", "Target Unit": "", "Unit Factor": "", "Raw Rows Used": 0, "Status": "", "Note": ""}
        spec_id = (header, cls_l, grp_l, prop_in, pattern, unit_bp, sign)
        if spec_id in seen_specs:
            cov["Status"] = "DUPLICATE BLUEPRINT ROW - ignored"
            cov["Note"] = "Row is repeated in Blueprint_std; counted once in the normalized raw view"
            coverage_rows.append(cov)
            continue
        seen_specs.add(spec_id)
        if tkey in skip_tables:
            cov["Status"], cov["Note"] = "NO COUNTERPART - custom section", skip_tables[tkey]
            coverage_rows.append(cov)
            continue
        if pattern.startswith("daily"):
            cov["Status"], cov["Note"] = "NO COUNTERPART - daily pattern", "Raw workbook is monthly only"
            coverage_rows.append(cov)
            continue
        eff_cls, eff_prop = cls_l, prop_in
        if (tkey, cls_l, prop_in) in custom_overrides:
            eff_cls, eff_prop, cov["Note"] = custom_overrides[(tkey, cls_l, prop_in)]
        if eff_cls not in class_to_raw:
            cov["Status"], cov["Note"] = "NO COUNTERPART - class not in raw data", f"Class '{cls_in}' is not in the raw workbook"
            coverage_rows.append(cov)
            continue
        fkey, coll, id_col = class_to_raw[eff_cls]
        cov["Raw DataFrame"], cov["Raw Collection"] = fkey, coll
        cats, gk = None, None
        if grp_l not in ("all", ""):
            gk = (cls_l, grp_l)
            if gk not in group_assets:
                gk = ("generator", grp_l)
            if gk not in group_assets:
                cov["Status"], cov["Note"] = "UNKNOWN GROUP", f"Class '{cls_in}' + Group '{grp_in}' is not defined on the Groups sheet"
                coverage_rows.append(cov)
                continue
            cats = group_assets[gk]
        printed_summary, generated = None, ""
        if pattern == "monthly-summary":
            gl = "all" if cats is None else group_label.get((cls_l, grp_l), group_label.get(("generator", grp_l), grp_in))
            generated = f"{cls_in}-{gl}-{prop_in}-Total"
            printed_summary = map_printed_name(generated, name_map)
        derived_components = derived_measures.get((fkey, coll, eff_prop))
        raw_col = None if (eff_cls, eff_prop) in no_raw_notes else property_to_raw_column.get((fkey, coll), {}).get(eff_prop)
        if raw_col is None:
            note_text = no_raw_notes.get((eff_cls, eff_prop), f"No '{eff_prop}' column for {fkey} / {coll}")
            if printed_summary is not None:
                key_only = normalize_text(printed_summary)
                pv_only = pd.DataFrame(np.nan, index=[key_only], columns=month_labels)
                if tkey in extracted:
                    extracted[tkey] = pd.concat([extracted[tkey], pv_only])
                else:
                    extracted[tkey] = pv_only
                    extracted_display[tkey], extracted_names[tkey], extracted_raw_ids[tkey] = {}, {}, set()
                    extracted_idonly[tkey], extracted_rate[tkey] = set(), use_mean
                extracted_raw_ids[tkey].add(generated)
                extracted_display[tkey][key_only] = printed_summary
                extracted_names[tkey][key_only] = generated
                extracted_idonly[tkey].add(key_only)
                cov["Status"], cov["Note"] = "IDENTIFIER ONLY (no raw measure)", note_text + "; row identifier validated, values not derivable"
            else:
                cov["Status"], cov["Note"] = "NO COUNTERPART - no raw measure", note_text
            coverage_rows.append(cov)
            continue
        cov["Raw Column"] = raw_col
        if derived_components:
            cov["Note"] = (cov["Note"] + "; " if cov["Note"] else "") + f"{eff_prop} derived per generator as the sum of: {', '.join(derived_components)}"
        needed_raw_columns = list(derived_components) if derived_components else [raw_col]
        missing_raw_columns = [c for c in needed_raw_columns if c not in raw_frames[fkey].columns]
        if missing_raw_columns:
            cov["Status"] = "NO COUNTERPART - raw column not in the workbook"
            cov["Note"] = (cov["Note"] + "; " if cov["Note"] else "") + f"The raw {fkey} sheet has no column {missing_raw_columns} (columns found: {list(raw_frames[fkey].columns)})"
            print(f"  WARNING: Blueprint row ({header} / {cls_in} / {grp_in} / {prop_in}) reads raw column(s) {missing_raw_columns} that are not on the raw sheet; the row is listed as 'raw column not in the workbook'")
            coverage_rows.append(cov)
            continue
        um = re.search(r"\(([^)]*)\)\s*$", raw_col)
        raw_unit = um.group(1).strip().lower() if um else "-"
        raw_unit = "hours" if raw_unit == "h" else raw_unit
        part = raw_parts.get((fkey, coll))
        if part is None:
            part = raw_frames[fkey].iloc[0:0]
        sub = part
        if cats is not None:
            mask_key = (fkey, coll, gk)
            if mask_key not in group_mask_cache:
                pkey = (fkey, coll)
                if pkey not in part_key_cache:
                    if coll == "Generator.Fuels":
                        kc = part["Parent Name"].map(parent_cat).fillna("")
                        kn = part["Parent Name"].astype(str)
                    else:
                        kc = part["Category"].astype(str).str.strip().str.lower()
                        kn = part["Child Name"].astype(str)
                    part_key_cache[pkey] = (kc, kn.str.replace(r"\s+", " ", regex=True).str.strip())
                key_cat, key_name = part_key_cache[pkey]
                keep_mask = key_cat.isin(cats)
                for rule_cat_l, rule_strings in group_extra_rules.get(gk, []):
                    in_rule_cat = key_cat == rule_cat_l
                    name_hit = pd.Series(False, index=part.index)
                    for rule_string in rule_strings:
                        name_hit = name_hit | key_name.str.contains(re.escape(rule_string), case=extra_include_match_case, na=False)
                    keep_mask = keep_mask | (in_rule_cat & name_hit)
                group_mask_cache[mask_key] = keep_mask
            sub = part[group_mask_cache[mask_key]]
        if derived_components:
            sub = sub.copy()
            sub[raw_col] = sub[derived_components].sum(axis=1, min_count=1)
        sub = sub[["Parent Name", "Collection", "Child Name", "Category", "Month Label", raw_col]].copy()
        if printed_summary is not None:
            sub["Report Name"] = printed_summary
            hint_src = printed_summary
        else:
            rn_key = (fkey, coll, id_col)
            if rn_key not in report_name_cache:
                id_str = part[id_col].astype(str)
                report_name_cache[rn_key] = id_str.map({s: map_printed_name(s, name_map) for s in id_str.unique()})
            sub["Report Name"] = report_name_cache[rn_key].loc[sub.index]
            hint_src = header
        hm = re.search(r"\(([^()]*)\)\s*$", hint_src.strip())
        target = unit_bp if unit_bp != "" else (hm.group(1).strip() if hm else raw_unit)
        t_l, f_l, thousand = target.lower().strip(), raw_unit, 1.0
        if t_l.startswith("1000·"):
            t_l, thousand = t_l[len("1000·"):], 1.0 / 1000.0
        t_l = "hours" if t_l == "h" else t_l
        if t_l == f_l:
            factor = 1.0 * thousand
        elif (f_l, t_l) in unit_rules:
            factor = unit_rules[(f_l, t_l)] * thousand
        else:
            factor = None
        cov["Raw Unit"], cov["Target Unit"] = raw_unit, target
        if factor is None:
            cov["Status"], cov["Note"] = "NO UNIT RULE", f"UnitConversion has no rule {raw_unit} -> {target}"
            coverage_rows.append(cov)
            continue
        cov["Unit Factor"] = factor * sign
        sub["Value"] = sub[raw_col] * factor * sign
        if section_special_factor.get(tkey):
            sub["Value"] = sub["Value"] * normalize_series(sub["Child Name"]).map(contract_factor).fillna(1.0)
        sub["Report Key"] = normalize_series(sub["Report Name"])
        cov["Raw Rows Used"] = int(len(sub))
        pv = sub.groupby(["Report Key", "Month Label"])["Value"].agg("mean" if use_mean else "sum").dropna().unstack("Month Label").reindex(columns=month_labels)
        by_key = sub.groupby("Report Key")
        disp = by_key["Report Name"].first().to_dict()
        names = by_key[id_col].agg(lambda s: " + ".join(sorted(set(str(x) for x in s)))).to_dict()
        ids = set(str(x) for x in sub[id_col]) if printed_summary is None else {generated}
        if tkey in extracted:
            extracted[tkey] = extracted[tkey].add(pv, fill_value=0.0)
            extracted_display[tkey].update({k: v for k, v in disp.items() if k not in extracted_display[tkey]})
            for k, v in names.items():
                extracted_names[tkey][k] = (extracted_names[tkey][k] + " + " + v) if k in extracted_names[tkey] else v
            extracted_raw_ids[tkey] |= ids
        else:
            extracted[tkey] = pv
            extracted_display[tkey] = dict(disp)
            extracted_names[tkey] = names
            extracted_raw_ids[tkey] = set(ids)
            extracted_idonly[tkey] = set()
            extracted_rate[tkey] = use_mean
        if derived_components:
            extracted_derived_keys.setdefault(tkey, set()).update(pv.index)
        cov["Status"] = "EXTRACTED" if not derived_components else "EXTRACTED (derived measure)"
        coverage_rows.append(cov)
    table_order.sort(key=section_sort_key)
    scope_missing_from_blueprint = [t for t in in_scope_tables if t not in table_order]
    print(f"  Scope: {len(in_scope_tables)} Standard sections in scope; {len(out_of_scope_tables)} Blueprint_std sections outside the scope were excluded")
    if scope_missing_from_blueprint:
        print(f"  WARNING: in-scope section(s) not found in Blueprint_std: {scope_missing_from_blueprint}")
    cov_df = pd.DataFrame(coverage_rows)
    if not cov_df.empty:
        print(f"  Blueprint_std: {len(cov_df)} rows, {len(table_order)} sections; raw measure found for "
              f"{int(cov_df['Status'].str.startswith('EXTRACTED').sum())} rows (of which derived: {int((cov_df['Status'] == 'EXTRACTED (derived measure)').sum())}), "
              f"identifier-only {int((cov_df['Status'] == 'IDENTIFIER ONLY (no raw measure)').sum())}, "
              f"duplicate rows ignored {int((cov_df['Status'] == 'DUPLICATE BLUEPRINT ROW - ignored').sum())}")
    return (extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys,
            cov_df, table_order, out_of_scope_tables, blueprint_titles)
def build_raw_standard_tables(table_order, extracted, extracted_display, extracted_idonly, extracted_rate, blueprint_titles, month_labels, raw_years):
    """Raw Standard sections in the normalized layout (row title + months + Tot-YYYY + Total). Returns raw_standard_tables, raw_standard_idonly."""
    raw_standard_tables, raw_standard_idonly = {}, {}
    for tkey in table_order:
        if tkey not in extracted:
            continue
        tbl = extracted[tkey].reindex(columns=month_labels)
        wide = {}
        for yr in raw_years:
            ycols = [m for m in month_labels if m.endswith(str(yr))]
            for m in ycols:
                wide[m] = tbl[m]
            wide[f"Tot-{yr}"] = tbl[ycols].mean(axis=1) if extracted_rate[tkey] else tbl[ycols].sum(axis=1, min_count=1)
        wide["Total"] = tbl[month_labels].mean(axis=1) if extracted_rate[tkey] else tbl[month_labels].sum(axis=1, min_count=1)
        wide_df = pd.DataFrame(wide)
        wide_df.insert(0, "", [extracted_display[tkey].get(k, k) for k in wide_df.index])
        raw_standard_tables[tkey] = {"title": blueprint_titles[tkey], "data": wide_df.reset_index(drop=True)}
        raw_standard_idonly[tkey] = set(extracted_idonly[tkey])
    return raw_standard_tables, raw_standard_idonly
def build_reports(plexos_sr_path, plexos_sr_rows, plexos_rr_path, plexos_rr_rows, raw_standard_tables, raw_ratings_tables):
    """Report dictionary (Raw = normalized raw data, PLEXOS = parsed report) for the Standard and Ratings reports."""
    return {"Standard Report": {"PLEXOS_path": plexos_sr_path, "PLEXOS_rows": plexos_sr_rows, "Raw_tables": raw_standard_tables,
                                "PLEXOS_tables": {}, "PLEXOS_format_issues": pd.DataFrame()},
            "Ratings Report": {"PLEXOS_path": plexos_rr_path, "PLEXOS_rows": plexos_rr_rows, "Raw_tables": raw_ratings_tables,
                               "PLEXOS_tables": {}, "PLEXOS_format_issues": pd.DataFrame()}}
def parse_reports_into_sections(reports, in_scope_tables, used_in_model_path, used_in_datamodel_tables, table_order):
    """Parse every report into sections, apply the in-scope and Used in DataModel filters (updates reports and table_order in place).
    Returns all_plexos_section_keys."""
    all_plexos_section_keys = {}
    for report_name, report_config in reports.items():
        plexos_tables, plexos_format_issues, _, _ = parse_plexos_report_sections(
            plexos_rows=report_config["PLEXOS_rows"], report_name=report_name,
            in_scope_tables=in_scope_tables if report_name == "Standard Report" else None)
        all_plexos_section_keys[report_name] = list(plexos_tables.keys())
        raw_count = lambda: len(reports[report_name]["Raw_tables"])
        if report_name == "Standard Report":
            if used_in_model_path != "":
                plexos_dropped = sorted(set(plexos_tables) - used_in_datamodel_tables, key=section_sort_key)
                plexos_tables = filter_tables_by_keys(plexos_tables, used_in_datamodel_tables)
                reports[report_name]["Raw_tables"] = filter_tables_by_keys(reports[report_name]["Raw_tables"], used_in_datamodel_tables)
                all_plexos_section_keys[report_name] = list(plexos_tables.keys())
                table_order[:] = [t for t in table_order if t in used_in_datamodel_tables]
                print(f"[{report_name}] Tables kept (in scope and Used in DataModel): Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
                if plexos_dropped:
                    print(f"[{report_name}] In-scope PLEXOS table(s) dropped (not marked 'Used in DataModel'): {plexos_dropped}")
            else:
                print(f"[{report_name}] 'Used in DataModel' filter skipped -- all in-scope sections kept: Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
        else:
            print(f"[{report_name}] 'Used in DataModel' filter skipped (not applicable to named sections) -- all sections kept: Raw={raw_count()} (no raw counterpart), PLEXOS={len(plexos_tables)}")
            print(f"[{report_name}] PLEXOS section keys found (raw, pre-alias): {sorted(plexos_tables.keys())}")
        report_config["PLEXOS_tables"] = plexos_tables
        report_config["PLEXOS_format_issues"] = plexos_format_issues
    return all_plexos_section_keys
def apply_retired_resource_filter(reports, retired_full_path, results_folder, output_file_name):
    """Remove retired resources from both sides of both reports, print the counts and write the Ratings removal list.
    Returns retired_removal_log, ratings_retired_removed_export, output_path."""
    retired_removal_log, ratings_export = remove_retired_resources(reports=reports, retired_full_path=retired_full_path)
    print(f"Rows removed as retired resources (both sides, both reports): {len(retired_removal_log)}")
    output_path = save_results_csv(ratings_export, results_folder, output_file_name)
    print(f"Ratings Report retired-resource removal list written to: {output_path} ({len(ratings_export)} row(s))")
    return retired_removal_log, ratings_export, output_path
def exclude_raw_only_rows(standard_config, exclude_rules, extracted_names):
    """Drop raw rows that are NOT printed in the PLEXOS report and match an exclusion rule ({table: [name fragments]}); updates the raw tables in place.
    Returns a DataFrame logging the excluded rows."""
    exclusion_rows = []
    for table_number, fragments in exclude_rules.items():
        if table_number not in standard_config["Raw_tables"] or table_number not in standard_config["PLEXOS_tables"]:
            continue
        raw_data = standard_config["Raw_tables"][table_number]["data"]
        px_data = standard_config["PLEXOS_tables"][table_number]["data"]
        raw_norm = normalize_series(raw_data.iloc[:, 0])
        px_norm = set(normalize_series(px_data.iloc[:, 0]))
        names_lookup = extracted_names.get(table_number, {})
        drop_mask = pd.Series(False, index=raw_data.index)
        for raw_index, raw_key in raw_norm.items():
            if raw_key in px_norm:
                continue
            haystack = (raw_key + " " + names_lookup.get(raw_key, "")).lower()
            matched_fragments = [f for f in fragments if normalize_text(f) in haystack]
            if matched_fragments:
                drop_mask[raw_index] = True
                exclusion_rows.append({"Table Number": table_number, "Raw Row Title": raw_data.loc[raw_index, raw_data.columns[0]],
                                       "Raw Data Name(s)": names_lookup.get(raw_key, ""), "Matched Rule": ", ".join(matched_fragments),
                                       "Reason": "Raw-only row that does not belong in this table (not printed in the PLEXOS report)"})
        standard_config["Raw_tables"][table_number]["data"] = raw_data[~drop_mask].reset_index(drop=True)
    return pd.DataFrame(exclusion_rows, columns=["Table Number", "Raw Row Title", "Raw Data Name(s)", "Matched Rule", "Reason"])
def record_step_result(step_number, passed, step_results, tc_name, status_text, suffix=""):
    """Store the step result, print 'Step N Status' and the running status of the whole test case."""
    passed = bool(passed)
    step_results[step_number] = passed
    print(f"Step {step_number} Status: {status_text[passed]}{suffix}")
    print_test_case_status(tc_name, step_number, step_results, status_text)
def print_status_checks(checks, status_text, indent="  "):
    """Print '<label>: PASS/FAIL' for every entry of the {label: bool} dictionary."""
    for label, passed in checks.items():
        print(f"{indent}{label}: {status_text[bool(passed)]}")
def has_rows_and_no_failures(results_df, failures_df):
    """True only when results_df has rows and failures_df is empty."""
    return bool((not results_df.empty) and failures_df.empty)
def save_structure_csv(structure_df, results_folder, file_name):
    """Write a structure/exception table to CSV with the header lists joined by ' | '. Returns the path."""
    csv_frame = structure_df.copy()
    for header_column in ("Raw Headers", "PLEXOS Headers"):
        csv_frame[header_column] = csv_frame[header_column].apply(lambda h: " | ".join(h))
    return save_results_csv(csv_frame, results_folder, file_name)
def save_step_summary(step_checks, step_results, status_text, results_folder, file_name, heading):
    """Build, save and print the step summary from [(step_number, check_label), ...]. Returns the summary DataFrame."""
    step_summary = pd.DataFrame([{"Step": n, "Check": label, "Status": status_text[step_results[n]]} for n, label in step_checks])
    save_results_csv(step_summary, results_folder, file_name)
    print(f"\n{heading}")
    print(step_summary.to_string(index=False))
    print(f"Results saved to: {Path(results_folder).resolve()}")
    return step_summary
def print_overall_result(step_results, label):
    """Print the final PASSED/FAILED line for the test case and return the overall result."""
    overall_pass = all(step_results.values())
    print(f"\n{'PASSED' if overall_pass else 'FAILED'}: {label}")
    return overall_pass
def build_occurrence_keys(labels):
    normalized_labels = (labels.fillna("").astype(str).str.replace(r"\s+", " ", regex=True).str.strip().str.lower())
    occurrence_numbers = normalized_labels.groupby(normalized_labels).cumcount().astype(str)
    return normalized_labels, (normalized_labels + "||" + occurrence_numbers).tolist()
def apply_openpyxl_header_style(worksheet, header_fill):
    for cell in worksheet[1]:
        cell.font = Font(bold=True)
        cell.fill = header_fill
def set_openpyxl_column_widths(worksheet, widths, start_column=1):
    for column_number, width in enumerate(widths, start=start_column):
        worksheet.column_dimensions[get_column_letter(column_number)].width = width
def pre_run_cell(info):
    cell_durations[info.cell_id] = {'start': time.time()}
def post_run_cell(result):
    cell_id = result.info.cell_id
    if cell_id in cell_durations and 'start' in cell_durations[cell_id]:
        duration = time.time() - cell_durations[cell_id]['start']
        cell_durations[cell_id]['duration'] = duration
ip = get_ipython()
if ip is not None:
    ip.events.register("pre_run_cell", pre_run_cell)
    ip.events.register("post_run_cell", post_run_cell)

#SHARED SIT FUNCTIONS
def clean_user_path(prompt_text):
    """Collect a file or folder path and remove surrounding quotation marks."""
    return input(prompt_text).strip().strip('"').strip("'")
def normalize_text(value):
    """Normalize whitespace and capitalization for reliable matching."""
    return re.sub(r"\s+", " ", str(value)).strip().lower()
def normalize_comparison_text(value):
    """Normalize whitespace and capitalization for row-title matching."""
    return normalize_text(value)
def validate_input_files(required_inputs, sit_step):
    """Validate required/optional inputs: [(input_label, input_path, is_required), ...]. Returns a results DataFrame."""
    validation_rows = []
    for input_label, input_path, input_required in required_inputs:
        input_path = str(input_path or "").strip()
        if input_path == "" and not input_required:
            validation_rows.append({"SIT Step": sit_step, "Input": input_label, "File Path": "(skipped)",
                                    "File Exists": "", "Status": "SKIPPED"})
            continue
        file_exists = Path(input_path).is_file()
        validation_rows.append({"SIT Step": sit_step, "Input": input_label, "File Path": input_path,
                                "File Exists": file_exists, "Status": "PASS" if file_exists else "FAIL"})
    validation_df = pd.DataFrame(validation_rows)
    failed_mask = validation_df["Status"].eq("FAIL")
    if failed_mask.any():
        failed_inputs = validation_df.loc[failed_mask, ["Input", "File Path"]]
        raise FileNotFoundError("One or more required input files were not found:\n"
                                + failed_inputs.to_string(index=False))
    return validation_df
def read_plexos_csv(report_path, report_label):
    """Read a PLEXOS CSV report and display its basic structure. Returns report_rows, maximum_column_count."""
    print(report_label)
    with open(report_path, "r", encoding="utf-8-sig", errors="replace", newline="") as report_file:
        report_rows = list(csv.reader(report_file))
    maximum_columns = max((len(row) for row in report_rows), default=0)
    print(f"Rows: {len(report_rows)}")
    print(f"Maximum Columns Found: {maximum_columns}")
    if report_rows:
        print(pd.DataFrame(report_rows[:5]).iloc[:, :6].to_string(index=False, header=False))
    else:
        print("WARNING: The report is empty.")
    return report_rows, maximum_columns
def load_raw_plexos_sheets(raw_workbook_path, standard_timeslice="All Periods"):
    """Load Battery, Region and Generator from one workbook open, keeping only the requested Timeslice when present."""
    sheet_to_variable = {"Battery": "df_bat", "Region": "df_reg", "Generator": "df_gen"}
    loaded_frames = {}
    with pd.ExcelFile(raw_workbook_path) as raw_excel:
        missing_sheets = [s for s in sheet_to_variable if s not in raw_excel.sheet_names]
        if missing_sheets:
            raise KeyError("The raw PLEXOS workbook is missing required worksheet(s): " + ", ".join(missing_sheets))
        for sheet_name, variable_name in sheet_to_variable.items():
            loaded = raw_excel.parse(sheet_name)
            if "Timeslice" in loaded.columns:
                timeslice_text = loaded["Timeslice"].fillna("").astype(str).str.strip()
                timeslice_keep = timeslice_text.str.lower() == standard_timeslice.lower()
                if timeslice_keep.any():
                    excluded_values = sorted(set(timeslice_text.loc[~timeslice_keep]))
                    loaded = loaded.loc[timeslice_keep].reset_index(drop=True)
                    print(f"  {variable_name} ({sheet_name}): Timeslice '{standard_timeslice}' rows used: "
                          f"{int(timeslice_keep.sum())} of {len(timeslice_keep)} "
                          f"(other Timeslice values left out: {excluded_values})")
                else:
                    print(f"  WARNING: {variable_name} ({sheet_name}) has a Timeslice column but no "
                          f"'{standard_timeslice}' rows (found: {sorted(set(timeslice_text))}); every row is used")
            loaded_frames[variable_name] = loaded
    return loaded_frames["df_bat"], loaded_frames["df_reg"], loaded_frames["df_gen"]
def add_normalized_month_labels(frame, frame_name, excel_serial_min=20000, excel_serial_max=80000):
    """Convert Excel serial, normal and text dates into 'Month Label'. Returns a datetime Series aligned to frame."""
    if "Month" not in frame.columns:
        raise KeyError(f"{frame_name} does not contain a 'Month' column.")
    month_raw = frame["Month"]
    month_is_number = month_raw.map(lambda value: isinstance(value, (int, float, np.integer, np.floating))
                                    and not isinstance(value, (bool, np.bool_)) and not pd.isna(value))
    month_number = pd.to_numeric(month_raw.where(month_is_number), errors="coerce")
    month_is_serial = month_is_number & month_number.between(excel_serial_min, excel_serial_max)
    month_is_bad_number = month_is_number & ~month_is_serial
    if month_is_bad_number.any():
        bad_samples = month_raw.loc[month_is_bad_number].drop_duplicates().head(8).tolist()
        print(f"  WARNING: {frame_name} has {int(month_is_bad_number.sum())} numeric Month value(s) that are not "
              f"valid Excel date serials ({excel_serial_min}-{excel_serial_max}); they are ignored. Sample: {bad_samples}")
    serial_datetime = pd.Timestamp("1899-12-30") + pd.to_timedelta(month_number.where(month_is_serial), unit="D")
    text_datetime = pd.to_datetime(month_raw.where(~month_is_number), errors="coerce", format="mixed")
    month_datetime = text_datetime.fillna(serial_datetime)
    if month_is_serial.any():
        print(f"  {frame_name}: {int(month_is_serial.sum())} Month value(s) were Excel date serial numbers "
              "and were converted to calendar months")
    if month_datetime.isna().any():
        print(f"  WARNING: {frame_name} has {int(month_datetime.isna().sum())} row(s) whose Month could not be read; "
              "they get no Month Label and drop out of the monthly columns")
    frame["Month Label"] = month_datetime.dt.strftime("%b-%Y")
    collections = sorted(frame["Collection"].dropna().astype(str).unique()) if "Collection" in frame.columns else []
    print(f"  {frame_name}: shape {frame.shape}, collections: {collections}")
    return month_datetime
def check_nonempty_file(file_path):
    """Check whether a path is a regular, nonempty file. Returns exists, size_bytes, not_empty."""
    try:
        file_stat = Path(file_path).stat()
        exists = S_ISREG(file_stat.st_mode)
        size_bytes = file_stat.st_size if exists else 0
    except OSError:
        exists, size_bytes = False, 0
    return exists, size_bytes, exists and size_bytes > 0
def build_group_extra_include_rules(df_gen, group_extra_includes, match_case=False):
    """Build and audit name-level group inclusion rules. Returns group_extra_rules, extra_include_df."""
    group_extra_rules = {}
    extra_include_rows = []
    generator_units = df_gen.loc[df_gen["Collection"].eq("Generator")].drop_duplicates("Child Name")
    generator_unit_category = generator_units["Category"].fillna("").astype(str).str.strip().str.lower()
    generator_unit_name = (generator_units["Child Name"].fillna("").astype(str)
                           .str.replace(r"\s+", " ", regex=True).str.strip())
    for group_key, rule_list in group_extra_includes.items():
        group_extra_rules[group_key] = []
        for rule_category, rule_strings in rule_list:
            normalized_rule_category = normalize_text(rule_category)
            cleaned_rule_strings = [s.strip() for s in rule_strings if str(s).strip()]
            group_extra_rules[group_key].append((normalized_rule_category, cleaned_rule_strings))
            names_in_category = generator_unit_name.loc[generator_unit_category.eq(normalized_rule_category)]
            matched_any = pd.Series(False, index=names_in_category.index, dtype=bool)
            for rule_string in cleaned_rule_strings:
                string_match = names_in_category.str.contains(re.escape(rule_string), case=match_case, na=False)
                matched_any = matched_any | string_match
                extra_include_rows.append({"Group": group_key[1], "Raw Category": rule_category,
                                           "Name Contains": rule_string, "Units Matched": int(string_match.sum()),
                                           "Matched Units": "; ".join(sorted(names_in_category.loc[string_match])),
                                           "Included": True})
                if int(string_match.sum()) == 0:
                    print(f"  WARNING: name-level include for {group_key[1].title()} "
                          f"('{rule_category}' containing '{rule_string}') matched no raw unit")
            left_out = names_in_category.loc[~matched_any]
            extra_include_rows.append({"Group": group_key[1], "Raw Category": rule_category,
                                       "Name Contains": "(none of the strings)", "Units Matched": int(len(left_out)),
                                       "Matched Units": "; ".join(sorted(left_out)), "Included": False})
            print(f"  {group_key[1].title()} name-level include from '{rule_category}': "
                  f"{int(matched_any.sum())} of {len(names_in_category)} units included, {len(left_out)} left out")
    extra_include_df = pd.DataFrame(extra_include_rows, columns=["Group", "Raw Category", "Name Contains",
                                                                 "Units Matched", "Matched Units", "Included"])
    return group_extra_rules, extra_include_df
def load_contract_factors(template_xl):
    """Load Contract_factors into a normalized resource-to-factor dictionary."""
    contract_factor_df = (template_xl.parse("Contract_factors", dtype=str)
                          .dropna(subset=["Resources_Plexos", "ConversionFactor"]))
    return {normalize_text(name): float(factor)
            for name, factor in zip(contract_factor_df["Resources_Plexos"], contract_factor_df["ConversionFactor"])}
def load_unit_conversion_rules(template_xl):
    """Load UnitConversion into a normalized (unit from, unit to) -> rate dictionary."""
    unit_conversion_df = (template_xl.parse("UnitConversion", dtype=str)
                          .dropna(subset=["UnitFrom", "UnitTo", "ConversionRate"]))
    return {(normalize_text(u_from), normalize_text(u_to)): float(rate)
            for u_from, u_to, rate in zip(unit_conversion_df["UnitFrom"], unit_conversion_df["UnitTo"],
                                          unit_conversion_df["ConversionRate"])}
def load_blueprint_standard(template_xl):
    """Load and normalize the Blueprint_std worksheet. Returns blueprint, blueprint_dups."""
    blueprint = template_xl.parse("Blueprint_std", dtype=str).fillna("")
    required_columns = ["Header", "Class", "Group", "Property", "Pattern", "Rate", "Unit", "Sign"]
    missing_columns = [c for c in required_columns if c not in blueprint.columns]
    if missing_columns:
        raise KeyError("Blueprint_std is missing required column(s): " + ", ".join(missing_columns))
    for column in required_columns:
        blueprint[column] = blueprint[column].astype(str).str.strip()
    blueprint_dups = sorted(set(blueprint.loc[blueprint.duplicated(keep="first"), "Header"]))
    return blueprint, blueprint_dups
def section_sort_key(section_key):
    """Sort section keys numerically, then by letter suffix (3, 3b, 10, 33c)."""
    section_text = str(section_key).strip().lower()
    number_match = re.match(r"^(\d+)", section_text)
    section_number = int(number_match.group(1)) if number_match else 10**6
    return section_number, re.sub(r"^\d+", "", section_text)
def load_used_in_datamodel_reference(used_in_model_path):
    """Load the Used in DataModel table-number set and category lookup. Returns used_in_datamodel_tables, table_category_lookup."""
    used_in_datamodel_tables = set()
    table_category_lookup = {}
    if not used_in_model_path:
        print("'Used in DataModel' reference workbook skipped -- no table filter or category lookup applied.")
        return used_in_datamodel_tables, table_category_lookup
    used_in_model_raw = pd.read_excel(used_in_model_path, header=None)
    table_number_pattern = re.compile(r"^\(?\s*(\d+[a-zA-Z]?)\s*\)?$")
    number_of_rows = len(used_in_model_raw)
    number_of_columns = used_in_model_raw.shape[1]
    column_b_values = used_in_model_raw.iloc[:, 1].tolist() if number_of_columns > 1 else [None] * number_of_rows
    column_c_values = used_in_model_raw.iloc[:, 2].tolist() if number_of_columns > 2 else [None] * number_of_rows
    column_d_values = used_in_model_raw.iloc[:, 3].tolist() if number_of_columns > 3 else [None] * number_of_rows
    for column_b, column_c, column_d in zip(column_b_values, column_c_values, column_d_values):
        label_cell = normalize_text(column_b) if pd.notna(column_b) else ""
        table_cell = str(column_c).strip() if pd.notna(column_c) else ""
        category_cell = str(column_d).strip() if pd.notna(column_d) else ""
        table_match = table_number_pattern.match(table_cell)
        if not table_match:
            continue
        table_key = table_match.group(1).lower()
        if category_cell:
            table_category_lookup[table_key] = category_cell
        if label_cell == "used in datamodel":
            used_in_datamodel_tables.add(table_key)
    print(f"'Used in DataModel' table numbers loaded: {len(used_in_datamodel_tables)}")
    print(f"  {sorted(used_in_datamodel_tables, key=section_sort_key)}")
    if not used_in_datamodel_tables:
        print("  WARNING: no table numbers were found marked 'Used in DataModel' -- every Standard Report table "
              "will be filtered out downstream. Confirm the workbook's column layout matches what this script expects.")
    print(f"Category lookup loaded for {len(table_category_lookup)} table number(s).")
    return used_in_datamodel_tables, table_category_lookup
def canonicalize_ratings_section_title(section_title):
    """Convert a Ratings Report title into its normalized section key."""
    day_token = (r"(?:mon|tue|tues|wed|weds|thu|thur|thurs|fri|sat|sun|"
                 r"sunday|monday|tuesday|wednesday|thursday|friday|saturday)")
    section_key = str(section_title).lower().strip()
    section_key = re.sub(r"\([^)]*\)", "", section_key)
    section_key = re.sub(rf"\b{day_token}\s*-\s*{day_token}\b", "", section_key)
    return re.sub(r"[^a-z0-9]+", "", section_key)
def parse_plexos_report_sections(plexos_rows, report_name, in_scope_tables=None):
    """Parse Standard/Ratings rows into section DataFrames (merges repeated chunks, pads/truncates ragged rows).
    Returns plexos_tables, plexos_format_issues, section_occurrences, discovered_section_keys."""
    plexos_tables = {}
    plexos_format_issues = []
    section_occurrences = {}
    is_standard_report = report_name == "Standard Report"
    standard_header_pattern = re.compile(r"^\(\s*(\d+[a-zA-Z]?)\s*\)")
    current_section = None
    current_title = None
    current_rows = []
    def finalize_section():
        if current_section is None:
            return
        cleaned_rows = [r for r in current_rows if any(str(c).strip() for c in r)]
        if not cleaned_rows:
            return
        section_occurrences[current_section] = section_occurrences.get(current_section, 0) + 1
        if current_section in plexos_tables:
            header = list(plexos_tables[current_section]["data"].columns)
            source_rows = cleaned_rows
        else:
            header = [str(c).strip() for c in cleaned_rows[0]]
            source_rows = cleaned_rows[1:]
        header_length = len(header)
        normalized_rows = []
        for source_row in source_rows:
            source_row = list(source_row)
            if len(source_row) != header_length:
                plexos_format_issues.append({"Table Number": current_section, "Table Title": current_title,
                                             "Expected Columns": header_length, "Actual Columns": len(source_row)})
                if len(source_row) < header_length:
                    source_row = source_row + [""] * (header_length - len(source_row))
                else:
                    source_row = source_row[:header_length]
            normalized_rows.append(source_row)
        new_section_df = pd.DataFrame(normalized_rows, columns=header)
        if current_section in plexos_tables:
            plexos_tables[current_section]["data"] = pd.concat(
                [plexos_tables[current_section]["data"], new_section_df], ignore_index=True)
        else:
            plexos_tables[current_section] = {"title": current_title, "data": new_section_df}
    for report_row in chain(plexos_rows, (None,)):
        if report_row is None:
            finalize_section()
            break
        non_blank_cells = [str(c).strip() for c in report_row if str(c).strip()]
        row_text = " ".join(non_blank_cells)
        if is_standard_report:
            header_match = standard_header_pattern.match(row_text)
            is_header_row = header_match is not None
        else:
            header_match = None
            is_header_row = len(non_blank_cells) == 1
        if is_header_row:
            finalize_section()
            current_section = (header_match.group(1).lower() if is_standard_report
                               else canonicalize_ratings_section_title(row_text))
            current_title = row_text
            current_rows = []
        elif current_section is not None:
            current_rows.append(report_row)
    split_sections = {k: v for k, v in section_occurrences.items() if v > 1}
    if split_sections:
        print(f"[{report_name}] WARNING: PLEXOS section(s) split into multiple chunks and merged: {split_sections}")
    discovered_section_keys = list(plexos_tables.keys())
    if is_standard_report and in_scope_tables is not None:
        out_of_scope_sections = [k for k in discovered_section_keys if k not in in_scope_tables]
        plexos_tables = {k: v for k, v in plexos_tables.items() if k in in_scope_tables}
        print(f"[{report_name}] In-scope sections kept: {len(plexos_tables)} of {len(discovered_section_keys)} "
              f"discovered; {len(out_of_scope_sections)} out-of-scope section(s) excluded: {out_of_scope_sections}")
        missing_scope = [k for k in in_scope_tables if k not in plexos_tables]
        if missing_scope:
            print(f"[{report_name}] WARNING: in-scope section(s) not found in the PLEXOS Standard Report: {missing_scope}")
    return plexos_tables, pd.DataFrame(plexos_format_issues), section_occurrences, discovered_section_keys
def apply_section_aliases(section_tables, section_aliases):
    """Rename section keys and merge sections that resolve to the same key. Returns remapped_tables, applied_aliases."""
    remapped_tables = {}
    applied_aliases = {}
    for original_key, section_value in section_tables.items():
        canonical_key = section_aliases.get(original_key, original_key)
        if original_key in section_aliases:
            applied_aliases[original_key] = canonical_key
        if canonical_key in remapped_tables:
            remapped_tables[canonical_key]["data"] = pd.concat(
                [remapped_tables[canonical_key]["data"], section_value["data"]], ignore_index=True)
        else:
            remapped_tables[canonical_key] = {"title": section_value["title"], "data": section_value["data"]}
    return remapped_tables, applied_aliases
def remove_retired_resources(reports, retired_full_path):
    """Remove retired resources from Raw and PLEXOS tables.
    Standard: exact normalized match. Ratings: contains match, longest names first.
    Returns retired_removal_log, ratings_retired_removed_export."""
    log_columns = ["Report", "Side", "Table Number", "Matched Retired Resource", "Removed Row Title"]
    ratings_columns = ["Matched Retired Resource", "Removed Row Title"]
    retired_removal_rows = []
    ratings_removed_rows = []
    if not retired_full_path:
        print("\nRetired resources workbook skipped -- no retired-resource filtering applied.")
        return pd.DataFrame(columns=log_columns), pd.DataFrame(columns=ratings_columns)
    retired_full_df = pd.read_excel(retired_full_path)
    consolidated_names = sorted({str(v).strip() for v in retired_full_df.iloc[:, 0] if str(v).strip()},
                                key=len, reverse=True)
    standard_retired_names = {normalize_text(name) for name in consolidated_names}
    ratings_lookup = [(name, normalize_text(name)) for name in consolidated_names]
    ratings_pattern = (re.compile("|".join(re.escape(n) for _, n in ratings_lookup)) if ratings_lookup else None)
    for report_name, report_config in reports.items():
        for side_label, tables in (("Raw", report_config["Raw_tables"]), ("PLEXOS", report_config["PLEXOS_tables"])):
            for table_number, table in tables.items():
                data = table["data"]
                if len(data.columns) == 0:
                    continue
                row_titles = data.iloc[:, 0].fillna("").astype(str).str.strip()
                normalized_titles = row_titles.str.replace(r"\s+", " ", regex=True).str.strip().str.lower()
                if report_name == "Standard Report":
                    keep_mask = ~normalized_titles.isin(standard_retired_names)
                    for removed_title in row_titles.loc[~keep_mask]:
                        retired_removal_rows.append({"Report": report_name, "Side": side_label,
                                                     "Table Number": table_number,
                                                     "Matched Retired Resource": normalize_text(removed_title),
                                                     "Removed Row Title": removed_title})
                else:
                    matched_retired = pd.Series([None] * len(row_titles), index=row_titles.index, dtype=object)
                    if ratings_pattern is not None:
                        candidate_mask = normalized_titles.str.contains(ratings_pattern, regex=True, na=False)
                        for row_index, normalized_title in normalized_titles.loc[candidate_mask].items():
                            for original_name, normalized_name in ratings_lookup:
                                if normalized_name in normalized_title:
                                    matched_retired.at[row_index] = original_name
                                    break
                    keep_mask = matched_retired.isna()
                    for removed_title, matched_name in zip(row_titles.loc[~keep_mask], matched_retired.loc[~keep_mask]):
                        retired_removal_rows.append({"Report": report_name, "Side": side_label,
                                                     "Table Number": table_number,
                                                     "Matched Retired Resource": matched_name,
                                                     "Removed Row Title": removed_title})
                        ratings_removed_rows.append({"Matched Retired Resource": matched_name,
                                                     "Removed Row Title": removed_title})
                table["data"] = data.loc[keep_mask].reset_index(drop=True)
    print(f"\nRetired resources loaded (consolidated list): {len(consolidated_names)}")
    print(f"  Applied to Standard Report via exact match: {len(standard_retired_names)} name(s)")
    print(f"  Applied to Ratings Report via contains match: {len(consolidated_names)} name(s)")
    return (pd.DataFrame(retired_removal_rows, columns=log_columns),
            pd.DataFrame(ratings_removed_rows, columns=ratings_columns))
def remove_plexos_structural_rows(reports):
    """Remove blank, Total and parenthesized rows from PLEXOS tables. Returns {(report_name, table_number): rows_removed}."""
    structural_rows_removed = {}
    for report_name, report_config in reports.items():
        for table_number, table in report_config["PLEXOS_tables"].items():
            data = table["data"]
            if len(data.columns) == 0:
                structural_rows_removed[(report_name, table_number)] = 0
                continue
            normalized_labels = (data.iloc[:, 0].fillna("").astype(str)
                                 .str.replace(r"\s+", " ", regex=True).str.strip().str.lower())
            structural_mask = (normalized_labels.eq("") | normalized_labels.eq("total")
                               | normalized_labels.str.startswith("("))
            structural_rows_removed[(report_name, table_number)] = int(structural_mask.sum())
            table["data"] = data.loc[~structural_mask].reset_index(drop=True)
    return structural_rows_removed
def build_row_title_counters(reports):
    """Build normalized row-title occurrence counters and display lookups.
    Returns raw_counters, raw_displays, plexos_counters, plexos_displays (each keyed by report, then table)."""
    raw_counters, raw_displays, plexos_counters, plexos_displays ={},{},{},{}
    for report_name, report_config in reports.items():
        raw_counters[report_name], raw_displays[report_name] = {},{}
        plexos_counters[report_name], plexos_displays[report_name] = {},{}
        for tables, counter_store, display_store in (
                (report_config["Raw_tables"], raw_counters[report_name], raw_displays[report_name]),
                (report_config["PLEXOS_tables"], plexos_counters[report_name], plexos_displays[report_name])):
            for table_number, table in tables.items():
                data = table["data"]
                if len(data.columns) == 0:
                    counter_store[table_number] = Counter()
                    display_store[table_number] = {}
                    continue
                original_titles = [str(v).strip() for v in data.iloc[:, 0]]
                normalized_titles = [normalize_text(t) for t in original_titles]
                counter_store[table_number] = Counter(normalized_titles)
                display_map = {}
                for original_title, normalized_title in zip(original_titles, normalized_titles):
                    display_map.setdefault(normalized_title, original_title)
                display_store[table_number] = display_map
    return raw_counters, raw_displays, plexos_counters, plexos_displays
def calculate_prioritization_index(matched_rows, rows_on_both_sides, total_plexos_rows, total_raw_rows):
    """Calculate the Step 2 base prioritization index."""
    matched_vs_both = matched_rows / rows_on_both_sides if matched_rows > 0 and rows_on_both_sides > 0 else 1
    matched_vs_plexos = matched_rows / total_plexos_rows if total_plexos_rows > 0 else 0
    matched_vs_raw = matched_rows / total_raw_rows if total_raw_rows > 0 else 0
    both_vs_plexos = rows_on_both_sides / total_plexos_rows if total_plexos_rows > 0 else 0
    both_vs_raw = rows_on_both_sides / total_raw_rows if total_raw_rows > 0 else 0
    return round(1 - (matched_vs_both * matched_vs_plexos * matched_vs_raw * both_vs_plexos * both_vs_raw), 4)
def find_normalized_column(dataframe, normalized_column_name):
    """Find a column ignoring spaces/punctuation/case ('Time Slice', 'time_slice' -> 'timeslice')."""
    normalized_target = re.sub(r"[^a-z0-9]", "", str(normalized_column_name).lower())
    for column_name in dataframe.columns:
        if re.sub(r"[^a-z0-9]", "", str(column_name).lower()) == normalized_target:
            return column_name
    return None
def convert_month_value_to_label(month_value):
    """Convert a date, date text or Excel date serial to Mon-YYYY. Returns None when it cannot be converted."""
    if isinstance(month_value, (bool, np.bool_)):
        return None
    month_timestamp = pd.NaT
    if isinstance(month_value, (int, float, np.integer, np.floating)):
        if pd.isna(month_value):
            return None
        if 20000 <= month_value <= 80000:
            month_timestamp = pd.Timestamp("1899-12-30") + pd.Timedelta(days=float(month_value))
    else:
        try:
            month_timestamp = pd.Timestamp(pd.to_datetime(month_value))
        except (ValueError, TypeError, OverflowError):
            return None
    if pd.isna(month_timestamp):
        return None
    return month_timestamp.strftime("%b-%Y")
def prepare_timeslice_sheet(raw_frame, timeslice_value="All Periods"):
    """Prepare a raw worksheet for Timeslice validation (adds 'ML' month label and 'is_ap' flag).
    Returns prepared_frame, timeslice_column, timeslice_value_count."""
    timeslice_column = find_normalized_column(raw_frame, "timeslice")
    if timeslice_column is None:
        return None, None, 0
    timeslice_text = raw_frame[timeslice_column].fillna("").astype(str).str.strip().str.lower()
    timeslice_value_count = int(timeslice_text.nunique(dropna=False))
    if timeslice_value_count < 2:
        return None, timeslice_column, timeslice_value_count
    prepared_frame = raw_frame.copy()
    month_codes, month_uniques = pd.factorize(prepared_frame["Month"])
    month_labels_unique = np.array([convert_month_value_to_label(v) for v in month_uniques] + [None], dtype=object)
    prepared_frame["ML"] = month_labels_unique[month_codes]
    prepared_frame["is_ap"] = timeslice_text.eq(str(timeslice_value).strip().lower()).to_numpy()
    return prepared_frame, timeslice_column, timeslice_value_count
def build_occurrence_keys(labels):
    """Create keys that distinguish duplicate normalized row titles (e.g. 'arlington||0', 'arlington||1')."""
    normalized_labels = (labels.fillna("").astype(str).str.replace(r"\s+", " ", regex=True).str.strip().str.lower())
    occurrence_numbers = normalized_labels.groupby(normalized_labels).cumcount().astype(str)
    return normalized_labels, (normalized_labels + "||" + occurrence_numbers).tolist()
def calculate_pair_percent_error(pair_plexos, pair_raw, has_plexos, has_raw, raw_identifier_only, column_mask, zero_threshold):
    """Calculate row sums, percent error ((PLEXOS - Raw) / Raw), notes and the undefined mask.
    Returns plexos_sum, raw_sum, percent_error, percent_note, undefined_mask."""
    both_present = has_plexos & has_raw
    percent_eligible = both_present & ~raw_identifier_only
    plexos_sum = np.where(has_plexos, np.nansum(pair_plexos[:, column_mask], axis=1), np.nan)
    raw_sum = np.where(has_raw & ~raw_identifier_only, np.nansum(pair_raw[:, column_mask], axis=1), np.nan)
    raw_sum_is_zero = np.abs(np.nan_to_num(raw_sum)) < zero_threshold
    plexos_sum_is_zero = np.abs(np.nan_to_num(plexos_sum)) < zero_threshold
    with np.errstate(divide="ignore", invalid="ignore"):
        percent_error = np.where(percent_eligible & ~raw_sum_is_zero, (plexos_sum - raw_sum) / raw_sum, np.nan)
    percent_error = np.where(percent_eligible & raw_sum_is_zero & plexos_sum_is_zero, 0.0, percent_error)
    percent_note = np.full(len(pair_plexos), "", dtype=object)
    percent_note[~both_present] = "n/a: only one side has this row"
    percent_note[both_present & raw_identifier_only] = "n/a: raw identifier only (no raw measure)"
    undefined_mask = percent_eligible & raw_sum_is_zero & ~plexos_sum_is_zero
    percent_note[undefined_mask] = "undefined: the Raw sum is 0 and the PLEXOS sum is not"
    return plexos_sum, raw_sum, percent_error, percent_note, undefined_mask
def apply_openpyxl_header_style(worksheet, header_fill):
    """Apply the shared header formatting to an openpyxl worksheet."""
    for cell in worksheet[1]:
        cell.font = Font(bold=True)
        cell.fill = header_fill
def set_openpyxl_column_widths(worksheet, widths, start_column=1):
    """Set openpyxl column widths beginning at start_column."""
    for column_number, width in enumerate(widths, start=start_column):
        worksheet.column_dimensions[get_column_letter(column_number)].width = width
def normalize_series(series):
    """Normalize a Series of labels: text, collapsed whitespace, lowercase."""
    return series.astype(str).str.replace(r"\s+", " ", regex=True).str.strip().str.lower()
def map_printed_name(name, name_map):
    """Return the maptable_ printed name for name, or name itself when it is not mapped."""
    return name_map.get(normalize_text(name), name)
def normalize_section_title(title):
    """Normalize a section title for comparison ('(n)' prefix and parentheticals removed, '&' -> 'and', native energy -> native load)."""
    normalized = str(title).lower().strip()
    normalized = re.sub(r'^\(\s*\d+[a-zA-Z]?\s*\)', '', normalized)
    normalized = normalized.replace('&', 'and')
    normalized = re.sub(r'\([^)]*\)', '', normalized)
    normalized = re.sub(r'\s+', ' ', normalized).strip()
    return 'system native load' if normalized == 'system native energy' else normalized
def print_test_case_status(tc_name, step_number, step_results, status_text):
    """Print the running PASS/FAIL status of the whole test case after a step."""
    print(f"TEST CASE {tc_name} - status after Step {step_number}: {status_text[all(step_results.values())]}")
def save_results_csv(df, results_folder, file_name):
    """Write df to results_folder/file_name without the index and return the path."""
    output_path = Path(results_folder) / file_name
    df.to_csv(output_path, index=False)
    return output_path
def filter_tables_by_keys(tables, allowed_keys):
    """Keep only the section tables whose key is in allowed_keys."""
    return {key: value for key, value in tables.items() if key in allowed_keys}
def filter_report_rows(results_df, report_name):
    """Rows of a results table for one report (an empty table is returned unchanged)."""
    return results_df[results_df['Report'] == report_name] if not results_df.empty else results_df
def get_mismatches(results_df, match_column):
    """Rows of a results table where the boolean match_column is False."""
    return results_df[~results_df[match_column]] if not results_df.empty else results_df
def all_rows_match(results_df, match_column):
    """True only when the table has rows and every value of match_column is True."""
    return bool((not results_df.empty) and results_df[match_column].all())
def build_section_lookup(results_df):
    """Lookup {(Report, Table Number): row dict} for a results table."""
    return {(r['Report'], r['Table Number']): r for r in results_df.to_dict('records')}
def load_maptables(template_xl):
    """Parse maptable_ sheets (col 1 = printed text, col 2 = text it replaces; header ignored; last listing wins).
    Returns name_map, name_map_sheet, map_exceptions, map_sheets."""
    name_map, name_map_sheet, map_exceptions = {}, {}, []
    map_sheets = [sn for sn in template_xl.sheet_names if sn.lower().startswith("maptable")]
    for sn in map_sheets:
        mdf = template_xl.parse(sn, header=0, dtype=str)
        printed_col = mdf.iloc[:, 0].tolist()
        replaced_col = mdf.iloc[:, 1].tolist() if mdf.shape[1] > 1 else [None] * len(mdf)
        for printed, replaced in zip(printed_col, replaced_col):
            if pd.isna(printed):
                continue
            if pd.isna(replaced) or str(replaced).strip() == "":
                map_exceptions.append({"Sheet": sn, "Name": str(printed).strip(), "Issue": "No mapping defined (column 2 is blank)"})
                continue
            mkey = normalize_text(replaced)
            if mkey in name_map:
                map_exceptions.append({"Sheet": sn, "Name": str(replaced).strip(),
                                       "Issue": f"Listed more than once; last listing used ('{name_map[mkey].strip()}' on {name_map_sheet[mkey]} replaced by '{str(printed).strip()}')"})
            name_map[mkey] = str(printed)
            name_map_sheet[mkey] = sn
    return name_map, name_map_sheet, map_exceptions, map_sheets
def load_template_groups(template_xl):
    """Parse the Groups sheet. Returns group_assets {(class, group): set of lowercase categories or None for 'all'} and group_label {(class, group): label}."""
    group_assets, group_label = {}, {}
    gdf = template_xl.parse("Groups", dtype=str).fillna("")
    for g_class, g_group, g_assets in zip(gdf["Class"], gdf["Group"], gdf["Assets"]):
        gkey = (g_class.strip().lower(), g_group.strip().lower())
        if g_assets.strip().lower() == "all":
            group_assets[gkey] = None
            group_label[gkey] = "all"
        else:
            assets_in_order = [a.strip() for a in g_assets.split(",") if a.strip()]
            group_assets[gkey] = set(a.lower() for a in assets_in_order)
            group_label[gkey] = "-".join(assets_in_order)
    return group_assets, group_label
def generate_report(notebook_filename=None):
    #1. Auto-detect the current notebook file if not specified
    if not notebook_filename:
        notebook_files = glob.glob("*.ipynb")
        if not notebook_files:
            return "No .ipynb files found in the current directory."
        #Fallback to the most recently modified notebook file
        notebook_filename = max(notebook_files, key=os.path.getmtime)
    #2. Read the notebook JSON file
    with open(notebook_filename, 'r', encoding='utf-8') as f:
        nb_data = json.load(f)
    report = {}
    current_header = "Intro / Setup"
    #3. Parse cell structure sequentially
    for cell in nb_data.get('cells', []):
        cell_type = cell.get('cell_type')
        cell_id = cell.get('id') #Unique ID matching IPython tracking
        #If it's a markdown cell, look for a header
        if cell_type == 'markdown':
            source = "".join(cell.get('source', []))
            for line in source.split('\n'):
                if line.strip().startswith('#'):
                    #Strip out Markdown syntax to get a clean title
                    current_header = line.replace('#', '').strip()
                    break #Use the highest level header found in this cell
        elif cell_type == 'code' and cell_id in cell_durations:
            duration = cell_durations[cell_id].get('duration', 0.0)
            report[current_header] = report.get(current_header, 0.0) + duration
    print(f"SUMMARY BY SECTION (File: {notebook_filename})")
    total_time = sum(report.values())
    if total_time == 0:
        print("No cell execution times recorded yet.")
        return
    for section, duration in report.items():
        pct = (duration / total_time) * 100
        print(f"{section:<25} : {duration:>6.2f}s ({pct:>5.1f}%)")
    print(f"Total Combined Code Runtime: {total_time:.2f} seconds\n")

################################################################################################################################################################################
#3.03A
################################################################################################################################################################################
def load_rating_raw_frames(raw_data_path, raw_timeslice_values, standard_timeslice, excel_serial_min, excel_serial_max):
    """The raw Generator frame of EVERY Timeslice value in raw_timeslice_values (each prepared like the Standard Report frames: Timeslice filter + Month labels, each proven to hold only that Timeslice, see load_raw_generator_for_timeslice), so the Ratings Report (one section per Timeslice) has a raw counterpart. The frames are kept in a dictionary so they are read ONCE and reused. load_raw_frames_cached keeps ONE prepared copy in the session cache: afterwards it is prepared again for standard_timeslice (also when a Timeslice fails), so every other test case finds the cache as it was. Returns {raw Timeslice value: (frame, proven True / False, proof text)}."""
    import io, contextlib
    rating_frames = {}
    try:
        for raw_timeslice_value in raw_timeslice_values:
            rating_frames[raw_timeslice_value] = load_raw_generator_for_timeslice(raw_data_path, raw_timeslice_value, excel_serial_min, excel_serial_max)
    finally:
        with contextlib.redirect_stdout(io.StringIO()):
            load_raw_frames_cached(raw_data_path=raw_data_path, standard_timeslice=standard_timeslice, excel_serial_min=excel_serial_min, excel_serial_max=excel_serial_max)
    return rating_frames
def build_raw_ratings_tables(rating_frames, rating_definitions, rating_sections, value_columns, raw_columns, month_labels, name_map, group_assets, group_extra_includes, extra_match_case, unit_factor, section_aliases):
    """The raw counterpart of the Ratings Report in the layout build_reports expects (raw_ratings_tables = {section key: {'title': text, 'data': DataFrame}}, the same layout as the raw Standard sections: first column = the row title, then the months, Tot-YYYY after each December and Total, the columns of raw_columns). One section per Timeslice of rating_frames (the key is the canonical Ratings section key through section_aliases: 'All Periods' -> 'atc', 'Off-Peak' -> 'offpeak', 'On-Peak' -> 'onpeak'; the title is the raw Timeslice value). Its rows are every kind of Ratings Report row of rating_definitions ('<name>:MW' = Generation, '<name>:MBTU' = Offtake of Generator.Fuels, see build_rating_raw_rows), the title of a row being the label the Ratings Report prints for that unit (spaces collapsed) or '<printed name>:<alias>' when the report has no such row; the rows follow the order of the Ratings Report section (rating_sections, from parse_rating_report_rows), raw units the report does not print come last. A Timeslice whose proof failed, or that has no raw row at all, gets no section. Returns raw_ratings_tables and a list of one dictionary per Timeslice (Timeslice, Section Key, Rows per alias, Total Rows, Note) for printing."""
    raw_ratings_tables, build_info = {}, []
    for raw_timeslice_value, (generator_frame, timeslice_proven, proof_text) in rating_frames.items():
        section_key = rating_timeslice_key(raw_timeslice_value, section_aliases)
        info = {"Timeslice": raw_timeslice_value, "Section Key": section_key, "Rows": {}, "Total Rows": 0, "Note": ""}
        build_info.append(info)
        if not timeslice_proven:
            info["Note"] = f"Timeslice proof failed ({proof_text}): no raw counterpart for this section"
            continue
        report_rows = rating_sections.get(section_key, {}).get("rows", [])
        table_rows = []
        for rating_definition in rating_definitions:
            measure = rating_definition["measure"]
            if not rating_definition_active(rating_definition, report_rows):
                continue
            if measure.get("may_be_missing"):
                pending_text = rating_measure_problem(generator_frame, measure)
                if pending_text != "":
                    pending_key = (rating_definition["alias"], measure.get("class", rating_definition["group_key"][0]), pending_text)
                    if pending_key not in RATING_PENDING_REPORTED:
                        RATING_PENDING_REPORTED.add(pending_key)
                        print(f"  RAW DATA NOT AVAILABLE YET: Ratings ':{rating_definition['alias']}' rows ({rating_definition['source']}): {pending_text}. These rows have no raw counterpart for now and are compared automatically as soon as the raw data holds the values.")
                    info["Rows"][rating_definition["alias"]] = info["Rows"].get(rating_definition["alias"], 0)
                    continue
            raw_rows = build_rating_raw_rows(generator_frame, month_labels, value_columns, name_map, group_assets, rating_definition["group_key"], group_extra_includes, extra_match_case, measure["collections"], measure["column"], rating_measure_factor(measure, unit_factor), measure)
            report_labels, ordered_keys = {}, []
            for report_row in report_rows:
                if report_row["alias"].lower() == rating_definition["alias"].lower() and report_row["name_key"] in raw_rows and report_row["name_key"] not in report_labels:
                    report_labels[report_row["name_key"]] = report_row["label"]
                    ordered_keys.append(report_row["name_key"])
            ordered_keys += sorted(name_key for name_key in raw_rows if name_key not in report_labels)
            for name_key in ordered_keys:
                row_title = report_labels.get(name_key, f"{raw_rows[name_key]['printed']}:{rating_definition['alias']}")
                table_rows.append([row_title] + [float(v) for v in raw_rows[name_key]["values"]])
            info["Rows"][rating_definition["alias"]] = info["Rows"].get(rating_definition["alias"], 0) + len(ordered_keys)
        info["Total Rows"] = len(table_rows)
        if len(table_rows) == 0:
            info["Note"] = "no raw Generator row belongs to the Ratings Report groups: no raw counterpart for this section"
            continue
        section_data = pd.DataFrame(table_rows, columns=list(raw_columns))
        if section_key in raw_ratings_tables:
            raw_ratings_tables[section_key]["data"] = pd.concat([raw_ratings_tables[section_key]["data"], section_data], ignore_index=True)
        else:
            raw_ratings_tables[section_key] = {"title": raw_timeslice_value, "data": section_data}
    return raw_ratings_tables, build_info
def parse_reports_into_sections(reports, in_scope_tables, used_in_model_path, used_in_datamodel_tables, table_order):
    """Parse every report into sections, apply the in-scope and Used in DataModel filters (updates reports and table_order in place).
    Returns all_plexos_section_keys. REPLACES the existing function: the only change is the Ratings message, which says '(no raw counterpart)' only when the Ratings Report really has no raw tables."""
    all_plexos_section_keys = {}
    for report_name, report_config in reports.items():
        plexos_tables, plexos_format_issues, _, _ = parse_plexos_report_sections(
            plexos_rows=report_config["PLEXOS_rows"], report_name=report_name,
            in_scope_tables=in_scope_tables if report_name == "Standard Report" else None)
        all_plexos_section_keys[report_name] = list(plexos_tables.keys())
        raw_count = lambda: len(reports[report_name]["Raw_tables"])
        if report_name == "Standard Report":
            if used_in_model_path != "":
                plexos_dropped = sorted(set(plexos_tables) - used_in_datamodel_tables, key=section_sort_key)
                plexos_tables = filter_tables_by_keys(plexos_tables, used_in_datamodel_tables)
                reports[report_name]["Raw_tables"] = filter_tables_by_keys(reports[report_name]["Raw_tables"], used_in_datamodel_tables)
                all_plexos_section_keys[report_name] = list(plexos_tables.keys())
                table_order[:] = [t for t in table_order if t in used_in_datamodel_tables]
                print(f"[{report_name}] Tables kept (in scope and Used in DataModel): Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
                if plexos_dropped:
                    print(f"[{report_name}] In-scope PLEXOS table(s) dropped (not marked 'Used in DataModel'): {plexos_dropped}")
            else:
                print(f"[{report_name}] 'Used in DataModel' filter skipped -- all in-scope sections kept: Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
        else:
            print(f"[{report_name}] 'Used in DataModel' filter skipped (not applicable to named sections) -- all sections kept: Raw={raw_count()}{' (no raw counterpart)' if raw_count() == 0 else ' (raw counterpart built from the raw data)'}, PLEXOS={len(plexos_tables)}")
            print(f"[{report_name}] PLEXOS section keys found (raw, pre-alias): {sorted(plexos_tables.keys())}")
        report_config["PLEXOS_tables"] = plexos_tables
        report_config["PLEXOS_format_issues"] = plexos_format_issues
    return all_plexos_section_keys

def build_section_name_maps(template_xl, blueprint, map_sheets, name_map_overrides=None):
    """Name maps that follow the Blueprint_std 'Maptable' column like the report generator does (see the template Read Me): a maptable_ sheet named in the Maptable cell of a section's rows is SECTION-ONLY: it applies only to the sections naming it and there its listings win over the shared sheets; every other maptable_ sheet is shared. Within one map a raw name listed twice uses its last listing (sheets in workbook order, rows top to bottom); matching ignores case and extra spaces; the printed text is kept exactly as typed (padding included). name_map_overrides (raw name -> printed name) is applied on top of the shared map (so it is inherited by every section map). Prints one line per section-only map. Returns shared_name_map, shared_name_map_sheet, section_name_maps ({tuple of sheet names: (name_map, name_map_sheet)}), section_headers ({Blueprint_std Header: tuple of sheet names}), map_exceptions (listings that were replaced by a later listing). REPLACES the single last-wins name_map for the sections that name a sheet."""
    sheet_lookup = {sn.strip().lower(): sn for sn in map_sheets}
    section_headers = {}
    if "Maptable" in blueprint.columns:
        for header_text, cell_text in zip(blueprint["Header"], blueprint["Maptable"]):
            named = [sheet_lookup.get(part.strip().lower()) for part in str(cell_text).split(",") if part.strip()]
            if len(named) > 0:
                missing_names = [part.strip() for part, sheet in zip([p for p in str(cell_text).split(",") if p.strip()], named) if sheet is None]
                if missing_names:
                    print(f"  WARNING: Blueprint_std Maptable names sheet(s) that are not in the template: {missing_names} (section {header_text})")
                section_headers[header_text] = tuple(sheet for sheet in named if sheet is not None)
    section_only_sheets = set(sheet for sheets in section_headers.values() for sheet in sheets)
    def read_pairs(sheet_name):
        mdf = template_xl.parse(sheet_name, header=0, dtype=str)
        printed_col = mdf.iloc[:, 0].tolist()
        replaced_col = mdf.iloc[:, 1].tolist() if mdf.shape[1] > 1 else [None] * len(mdf)
        return [(str(printed), str(replaced).strip()) for printed, replaced in zip(printed_col, replaced_col) if not pd.isna(printed) and not pd.isna(replaced) and str(replaced).strip() != ""]
    shared_name_map, shared_name_map_sheet, map_exceptions = {}, {}, []
    for sheet_name in map_sheets:
        if sheet_name in section_only_sheets:
            continue
        for printed, replaced in read_pairs(sheet_name):
            replaced_key = normalize_text(replaced)
            if replaced_key in shared_name_map:
                map_exceptions.append({"Sheet": sheet_name, "Name": replaced, "Issue": f"Listed more than once; last listing used ('{shared_name_map[replaced_key].strip()}' on {shared_name_map_sheet[replaced_key]} replaced by '{printed.strip()}')"})
            shared_name_map[replaced_key] = printed
            shared_name_map_sheet[replaced_key] = sheet_name
    if name_map_overrides:
        apply_name_map_overrides(shared_name_map, shared_name_map_sheet, name_map_overrides)
    section_name_maps = {}
    for sheets in sorted(set(section_headers.values())):
        section_map, section_map_sheet = dict(shared_name_map), dict(shared_name_map_sheet)
        for sheet_name in sheets:
            for printed, replaced in read_pairs(sheet_name):
                section_map[normalize_text(replaced)] = printed
                section_map_sheet[normalize_text(replaced)] = sheet_name
        section_name_maps[sheets] = (section_map, section_map_sheet)
        applies_to = [h.split(")")[0].strip("( ") for h, s in section_headers.items() if s == sheets]
        print(f"  Section-only name map {', '.join(sheets)}: used by section(s) {applies_to} ({len(section_map) - len(shared_name_map)} listing(s) added to the {len(shared_name_map)} shared name(s); its listings win)")
    return shared_name_map, shared_name_map_sheet, section_name_maps, section_headers, map_exceptions
def extract_blueprint_sections_by_section_map(blueprint, section_name_maps, section_headers, default_name_map, raw_frames, month_labels, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                                              in_scope_tables, class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """extract_blueprint_sections, run once per name map: the Blueprint_std rows of the sections that name a section-only maptable_ sheet (section_headers) are rebuilt with that section's name map (section_name_maps), every other row with default_name_map. The results are merged and returned in the same order as extract_blueprint_sections returns them: extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys, cov_df, table_order, out_of_scope_tables, blueprint_titles (table_order and the coverage table keep the Blueprint_std order)."""
    map_key_by_row = blueprint["Header"].map(lambda header_text: section_headers.get(header_text, ()))
    keys_in_order = list(dict.fromkeys(map_key_by_row.tolist()))
    merged = [{}, {}, {}, {}, {}, {}, {}]
    coverage_frames, out_of_scope_tables, blueprint_titles, tables_seen = [], set(), {}, []
    for map_key in keys_in_order:
        part_blueprint = blueprint[map_key_by_row.map(lambda row_key: row_key == map_key)]
        part_name_map = default_name_map if map_key == () else section_name_maps[map_key][0]
        part = extract_blueprint_sections(part_blueprint, raw_frames, month_labels, part_name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, in_scope_tables, class_to_raw,
                                          property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case)
        for position in range(7):
            merged[position].update(part[position])
        coverage_frames.append(part[7])
        out_of_scope_tables |= set(part[9])
        blueprint_titles.update(part[10])
        tables_seen.extend(t for t in part[8] if t not in tables_seen)
    position_in_blueprint = {}
    for header_text in blueprint["Header"]:
        header_match = re.match(r"^\(\s*(\w+)\s*\)", header_text)
        position_in_blueprint.setdefault(header_match.group(1).lower() if header_match else header_text.lower(), len(position_in_blueprint))
    table_order = sorted(tables_seen, key=lambda t: position_in_blueprint.get(t, 10 ** 6))
    cov_df = pd.concat(coverage_frames, ignore_index=True)
    if "Table" in cov_df.columns and len(cov_df) > 0:
        cov_df = cov_df.iloc[sorted(range(len(cov_df)), key=lambda i: (position_in_blueprint.get(cov_df["Table"].iloc[i], 10 ** 6), i))].reset_index(drop=True)
    return (merged[0], merged[1], merged[2], merged[3], merged[4], merged[5], merged[6], cov_df, table_order, out_of_scope_tables, blueprint_titles)
def apply_name_map_overrides(name_map, name_map_sheet, name_map_overrides):
    """Add / replace maptable_ entries from NAME_MAP_OVERRIDES ({raw (solution.zip) name: name printed in the PLEXOS Standard Report}). Updates name_map and name_map_sheet in place and prints one line per override: added, replacing a different template entry, or already the same (nothing changes). Returns the number of overrides that added or changed an entry."""
    changed = 0
    for override_raw_name, override_printed_name in name_map_overrides.items():
        override_key = normalize_text(override_raw_name)
        if override_key not in name_map:
            print(f"  Name map override added (not in the template maptable_ sheets): raw '{override_raw_name}' -> printed '{override_printed_name}'")
            changed += 1
        elif normalize_text(name_map[override_key]) != normalize_text(override_printed_name):
            print(f"  Name map override REPLACES the template entry: raw '{override_raw_name}' -> '{name_map[override_key]}' becomes '{override_printed_name}'")
            changed += 1
        else:
            print(f"  Name map override already in the template (no change): raw '{override_raw_name}' -> printed '{override_printed_name}'")
        name_map[override_key] = override_printed_name
        name_map_sheet[override_key] = "NAME_MAP_OVERRIDES"
    return changed
def canonical_month_header(header):
    """One spelling for a monthly / total column header so the same month compares equal whatever the year is written like: 'Jan-26', 'Jan-2026', 'January 2026', '2026-01' -> 'Jan-2026'; 'Tot-2026', 'Total 2026', '2026 Total' -> 'Tot-2026'; 'Total' / 'Grand Total' -> 'Total'; any other text is returned unchanged (stripped). Self-contained: it needs no notebook variables (unlike canonical_header)."""
    text = str(header).strip()
    low = re.sub(r"\s+", " ", text.lower().replace("_", " "))
    month_names = ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
    found = re.match(r"^(" + "|".join(month_names) + r")[a-z]*[-\s/'.]*(\d{2}|\d{4})$", low)
    if found:
        year_number = int(found.group(2))
        return f"{found.group(1).title()}-{year_number + 2000 if year_number < 100 else year_number}"
    found = re.match(r"^(\d{4})[-/](\d{1,2})(?:[-/]\d{1,2})?(?:\s.*)?$", low)
    if found and 1 <= int(found.group(2)) <= 12:
        return f"{month_names[int(found.group(2)) - 1].title()}-{found.group(1)}"
    found = re.match(r"^(?:tot|total)[-\s:_]*(\d{4})$", low) or re.match(r"^(\d{4})[-\s:_]*(?:tot|total)$", low)
    if found:
        return f"Tot-{found.group(1)}"
    return "Total" if low in ("total", "grand total", "tot") else text
def canonical_header_list(headers):
    """A table's header list with every value column header in the canonical spelling (the first column, the row-title column, is kept as it is)."""
    headers = [str(h) for h in headers]
    return headers[:1] + [canonical_month_header(h) for h in headers[1:]]
def drop_blank_trailing_columns(reports):
    """PLEXOS tables only (Standard and Ratings): remove every value column that does not exist in the report: a column whose header is blank (or was renamed '.1', '.2' by make_report_headers_unique) AND whose cells are all blank in every row. A trailing comma at the end of the report's header / data rows creates such a column; it was counted as a real column (81 instead of 80) and made every section fail the column-count and header checks. A blank-header column that holds any value is kept (it is real data). Run it BEFORE make_report_headers_unique. Stores the number removed on each table as table['blank_columns_ignored'] and prints one line. A blank-header column that does hold values is kept and named in a WARNING line. Returns the total number of columns removed and a list of (report, table, column position, header) for the columns removed."""
    removed_total, removed_detail, kept_with_values = 0, [], []
    for report_name, report_config in reports.items():
        for table_number, table in (report_config.get("PLEXOS_tables") or {}).items():
            data = table["data"]
            table["blank_columns_ignored"] = 0
            if data.shape[1] < 2:
                continue
            header_text = [str(c).strip() for c in data.columns]
            cell_text = np.char.strip(data.iloc[:, 1:].fillna("").astype(str).to_numpy().astype(str))
            cell_blank = (cell_text == "").all(axis=0) if cell_text.shape[0] > 0 else np.ones(cell_text.shape[1], dtype=bool)
            header_blank = np.array([re.match(r"^(\.\d+)?$", h) is not None for h in header_text[1:]], dtype=bool)
            drop_value_columns = header_blank & cell_blank
            for i in np.flatnonzero(header_blank & ~cell_blank).tolist():
                kept_with_values.append((report_name, table_number, i + 1, header_text[i + 1], int((cell_text[:, i] != "").sum())))
            if drop_value_columns.any():
                keep_positions = [0] + [i + 1 for i, drop in enumerate(drop_value_columns) if not drop]
                removed_detail.extend((report_name, table_number, i + 1, header_text[i + 1]) for i, drop in enumerate(drop_value_columns) if drop)
                table["data"] = data.iloc[:, keep_positions]
                table["blank_columns_ignored"] = int(drop_value_columns.sum())
                removed_total += int(drop_value_columns.sum())
    tables_touched = len(set((r, t) for r, t, _, _ in removed_detail))
    print(f"Blank columns that do not exist in the report (blank header, every cell blank) ignored: {removed_total} column(s) in {tables_touched} table(s)" + (f"; positions {sorted(set(p for _, _, p, _ in removed_detail))}" if removed_total else ""))
    for kept_report, kept_table, kept_position, kept_header, kept_count in kept_with_values:
        print(f"  WARNING: [{kept_report}] table {kept_table}: column {kept_position} has a blank header but {kept_count} value(s); it is real data, so it is KEPT and counted (check the report generator for a stray column)")
    return removed_total, removed_detail
def extract_blueprint_sections_by_section_map(blueprint, section_name_maps, section_headers, default_name_map, raw_frames, month_labels, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                                              in_scope_tables, class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """extract_blueprint_sections, run once per name map (the per-part summary lines of extract_blueprint_sections are not printed, because each part holds only some of the sections; ONE summary for the merged result is printed instead; every other line, such as a raw-column warning, is printed as before). REPLACES the existing function.  the Blueprint_std rows of the sections that name a section-only maptable_ sheet (section_headers) are rebuilt with that section's name map (section_name_maps), every other row with default_name_map. The results are merged and returned in the same order as extract_blueprint_sections returns them: extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys, cov_df, table_order, out_of_scope_tables, blueprint_titles (table_order and the coverage table keep the Blueprint_std order)."""
    import io, contextlib
    map_key_by_row = blueprint["Header"].map(lambda header_text: section_headers.get(header_text, ()))
    keys_in_order = list(dict.fromkeys(map_key_by_row.tolist()))
    merged = [{}, {}, {}, {}, {}, {}, {}]
    coverage_frames, out_of_scope_tables, blueprint_titles, tables_seen = [], set(), {}, []
    for map_key in keys_in_order:
        part_blueprint = blueprint[map_key_by_row.map(lambda row_key: row_key == map_key)]
        part_name_map = default_name_map if map_key == () else section_name_maps[map_key][0]
        captured_text = io.StringIO()
        with contextlib.redirect_stdout(captured_text):
            part = extract_blueprint_sections(part_blueprint, raw_frames, month_labels, part_name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, in_scope_tables, class_to_raw,
                                              property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case)
        for captured_line in captured_text.getvalue().splitlines():
            if not captured_line.startswith(("  Scope: ", "  WARNING: in-scope section(s) not found in Blueprint_std", "  Blueprint_std: ")):
                print(captured_line)
        for position in range(7):
            merged[position].update(part[position])
        coverage_frames.append(part[7])
        out_of_scope_tables |= set(part[9])
        blueprint_titles.update(part[10])
        tables_seen.extend(t for t in part[8] if t not in tables_seen)
    position_in_blueprint = {}
    for header_text in blueprint["Header"]:
        header_match = re.match(r"^\(\s*(\w+)\s*\)", header_text)
        position_in_blueprint.setdefault(header_match.group(1).lower() if header_match else header_text.lower(), len(position_in_blueprint))
    table_order = sorted(tables_seen, key=lambda t: position_in_blueprint.get(t, 10 ** 6))
    cov_df = pd.concat(coverage_frames, ignore_index=True)
    if "Table" in cov_df.columns and len(cov_df) > 0:
        cov_df = cov_df.iloc[sorted(range(len(cov_df)), key=lambda i: (position_in_blueprint.get(cov_df["Table"].iloc[i], 10 ** 6), i))].reset_index(drop=True)
    print(f"  Scope: {len(in_scope_tables)} Standard sections in scope; {len(out_of_scope_tables)} Blueprint_std sections outside the scope were excluded")
    if [t for t in in_scope_tables if t not in table_order]:
        print(f"  WARNING: in-scope section(s) not found in Blueprint_std: {[t for t in in_scope_tables if t not in table_order]}")
    if not cov_df.empty:
        print(f"  Blueprint_std: {len(cov_df)} rows, {len(table_order)} sections; raw measure found for {int(cov_df['Status'].str.startswith('EXTRACTED').sum())} rows (of which derived: {int((cov_df['Status'] == 'EXTRACTED (derived measure)').sum())}), "
              f"identifier-only {int((cov_df['Status'] == 'IDENTIFIER ONLY (no raw measure)').sum())}, duplicate rows ignored {int((cov_df['Status'] == 'DUPLICATE BLUEPRINT ROW - ignored').sum())}")
    return (merged[0], merged[1], merged[2], merged[3], merged[4], merged[5], merged[6], cov_df, table_order, out_of_scope_tables, blueprint_titles)
################################################################################################################################################################################
#3.03B
################################################################################################################################################################################
def add_rating_value_columns(row_comparison_results, rating_summary, rating_section_tables, rating_not_compared, not_present, max_names_shown=10):
    """Adds the Ratings Report VALUE comparison (raw Generation (GWh) vs the ':MW' rows, raw Offtake (BBtu) vs the ':MBTU' rows, one Timeslice per Ratings section) to the row-comparison results of PlexOS-3.03B, so PlexOS_3_03B_Row_Comparison_Results.csv shows the Ratings Report comparison too. One result row per section exists already; eight columns are appended AFTER the existing ones (the existing columns and values are not changed): 'Value Row Pairs', 'Value MATCH', 'Value DIFFERS', 'Value Only in PLEXOS', 'Value Only in Raw Data' (counts over the compared kinds of row, ':MW' and ':MBTU' together), 'Value Largest Absolute Difference', 'Value Status' (PASS when every compared row pair matches and nothing failed; FAIL otherwise; 'N/A - reason' when the section could not be compared) and 'Value Comparison Detail' (per kind of row: basis and counts, then the row pairs that are not MATCH, then anything that could not be compared). The rows of the Standard Report keep these columns blank. The value comparison is informational: it does not change 'Status' or any step result. rating_summary = one row per (section, kind of row) with Table Number, Row Pairs, MATCH, DIFFERS, Only in PLEXOS, Only in Raw Data, Excluded (removed earlier), Largest Absolute Difference, Ratings Rows Not Compared and Value Basis; rating_section_tables = {'Rat <section key>': {'frame': pair rows (PLEXOS row, then the Raw Data row)}}; rating_not_compared = rows with Table Number and Reason. Returns a new DataFrame."""
    count_columns = ["Value Row Pairs", "Value MATCH", "Value DIFFERS", "Value Only in PLEXOS", "Value Only in Raw Data"]
    result = row_comparison_results.copy()
    for count_column in count_columns:
        result[count_column] = pd.array([pd.NA] * len(result), dtype="Int64")
    result["Value Largest Absolute Difference"] = np.nan
    result["Value Status"] = ""
    result["Value Comparison Detail"] = ""
    summary_by_section = {section_key: group for section_key, group in rating_summary.groupby("Table Number", sort=False)} if len(rating_summary) > 0 else {}
    for row_label in result.index[result["Report"] == "Ratings Report"]:
        section_key = result.at[row_label, "Table Number"]
        reasons = rating_not_compared[rating_not_compared["Table Number"] == section_key]["Reason"].astype(str).tolist() if len(rating_not_compared) > 0 else []
        failure_reasons = list(dict.fromkeys(r for r in reasons if not r.startswith("the label does not end in")))
        section_summary = summary_by_section.get(section_key)
        if section_summary is None:
            not_compared_text = "; ".join(failure_reasons) if failure_reasons else "no Ratings value comparison was made for this section"
            result.at[row_label, "Value Status"] = "N/A - " + not_compared_text
            result.at[row_label, "Value Comparison Detail"] = "not compared: " + not_compared_text
            continue
        totals = {column_name: int(section_summary[column_name].sum()) for column_name in ("Row Pairs", "MATCH", "DIFFERS", "Only in PLEXOS", "Only in Raw Data")}
        parts = []
        for _, summary_row in section_summary.iterrows():
            part = f"{summary_row['Value Basis']}: {int(summary_row['Row Pairs'])} pair(s), {int(summary_row['MATCH'])} MATCH"
            for label_text, column_name in (("DIFFERS", "DIFFERS"), ("only in PLEXOS", "Only in PLEXOS"), ("only in Raw Data", "Only in Raw Data")):
                if int(summary_row[column_name]) > 0:
                    part += f", {int(summary_row[column_name])} {label_text}"
            if int(summary_row["Excluded (removed earlier)"]) > 0:
                part += f", {int(summary_row['Excluded (removed earlier)'])} row(s) left out on the PLEXOS and raw side (removed by the retired-resource filter)"
            parts.append(part)
        detail = " | ".join(parts)
        not_match_texts = []
        table_entry = rating_section_tables.get(f"Rat {section_key}")
        if table_entry is not None and len(table_entry["frame"]) > 0:
            pair_frame = table_entry["frame"]
            plexos_part, raw_part = pair_frame.iloc[0::2].reset_index(drop=True), pair_frame.iloc[1::2].reset_index(drop=True)
            for pair_position in range(len(plexos_part)):
                pair_status = str(plexos_part.at[pair_position, "Pair Status"])
                if pair_status != "MATCH":
                    pair_title = plexos_part.at[pair_position, "Row Title"] if plexos_part.at[pair_position, "Row Title"] != not_present else raw_part.at[pair_position, "Row Title"]
                    not_match_texts.append(f"'{str(pair_title).strip()}' {pair_status}")
        if not_match_texts:
            detail += " | not MATCH: " + "; ".join(not_match_texts[:max_names_shown]) + (f"; (+{len(not_match_texts) - max_names_shown} more)" if len(not_match_texts) > max_names_shown else "")
        if failure_reasons:
            detail += " | not compared: " + "; ".join(failure_reasons)
        for count_column, total_key in zip(count_columns, ("Row Pairs", "MATCH", "DIFFERS", "Only in PLEXOS", "Only in Raw Data")):
            result.at[row_label, count_column] = totals[total_key]
        result.at[row_label, "Value Largest Absolute Difference"] = float(section_summary["Largest Absolute Difference"].max())
        all_match = totals["Row Pairs"] > 0 and totals["DIFFERS"] == 0 and totals["Only in PLEXOS"] == 0 and totals["Only in Raw Data"] == 0 and len(failure_reasons) == 0
        result.at[row_label, "Value Status"] = "PASS" if all_match else "FAIL"
        result.at[row_label, "Value Comparison Detail"] = detail
    return result
def load_rating_raw_frames(raw_data_path, raw_timeslice_values, standard_timeslice, excel_serial_min, excel_serial_max):
    """The raw Generator frame of EVERY Timeslice value in raw_timeslice_values (each prepared like the Standard Report frames: Timeslice filter + Month labels, each proven to hold only that Timeslice, see load_raw_generator_for_timeslice), so the Ratings Report (one section per Timeslice) has a raw counterpart. The frames are kept in a dictionary so they are read ONCE and reused. load_raw_frames_cached keeps ONE prepared copy in the session cache: afterwards it is prepared again for standard_timeslice (also when a Timeslice fails), so every other test case finds the cache as it was. Returns {raw Timeslice value: (frame, proven True / False, proof text)}."""
    import io, contextlib
    rating_frames = {}
    try:
        for raw_timeslice_value in raw_timeslice_values:
            rating_frames[raw_timeslice_value] = load_raw_generator_for_timeslice(raw_data_path, raw_timeslice_value, excel_serial_min, excel_serial_max)
    finally:
        with contextlib.redirect_stdout(io.StringIO()):
            load_raw_frames_cached(raw_data_path=raw_data_path, standard_timeslice=standard_timeslice, excel_serial_min=excel_serial_min, excel_serial_max=excel_serial_max)
    return rating_frames
def build_raw_ratings_tables(rating_frames, rating_definitions, rating_sections, value_columns, raw_columns, month_labels, name_map, group_assets, group_extra_includes, extra_match_case, unit_factor, section_aliases):
    """The raw counterpart of the Ratings Report in the layout build_reports expects (raw_ratings_tables = {section key: {'title': text, 'data': DataFrame}}, the same layout as the raw Standard sections: first column = the row title, then the months, Tot-YYYY after each December and Total, the columns of raw_columns). One section per Timeslice of rating_frames (the key is the canonical Ratings section key through section_aliases: 'All Periods' -> 'atc', 'Off-Peak' -> 'offpeak', 'On-Peak' -> 'onpeak'; the title is the raw Timeslice value). Its rows are every kind of Ratings Report row of rating_definitions ('<name>:MW' = Generation, '<name>:MBTU' = Offtake of Generator.Fuels, see build_rating_raw_rows), the title of a row being the label the Ratings Report prints for that unit (spaces collapsed) or '<printed name>:<alias>' when the report has no such row; the rows follow the order of the Ratings Report section (rating_sections, from parse_rating_report_rows), raw units the report does not print come last. A Timeslice whose proof failed, or that has no raw row at all, gets no section. Returns raw_ratings_tables and a list of one dictionary per Timeslice (Timeslice, Section Key, Rows per alias, Total Rows, Note) for printing."""
    raw_ratings_tables, build_info = {}, []
    for raw_timeslice_value, (generator_frame, timeslice_proven, proof_text) in rating_frames.items():
        section_key = rating_timeslice_key(raw_timeslice_value, section_aliases)
        info = {"Timeslice": raw_timeslice_value, "Section Key": section_key, "Rows": {}, "Total Rows": 0, "Note": ""}
        build_info.append(info)
        if not timeslice_proven:
            info["Note"] = f"Timeslice proof failed ({proof_text}): no raw counterpart for this section"
            continue
        report_rows = rating_sections.get(section_key, {}).get("rows", [])
        table_rows = []
        for rating_definition in rating_definitions:
            measure = rating_definition["measure"]
            if not rating_definition_active(rating_definition, report_rows):
                continue
            if measure.get("may_be_missing"):
                pending_text = rating_measure_problem(generator_frame, measure)
                if pending_text != "":
                    pending_key = (rating_definition["alias"], measure.get("class", rating_definition["group_key"][0]), pending_text)
                    if pending_key not in RATING_PENDING_REPORTED:
                        RATING_PENDING_REPORTED.add(pending_key)
                        print(f"  RAW DATA NOT AVAILABLE YET: Ratings ':{rating_definition['alias']}' rows ({rating_definition['source']}): {pending_text}. These rows have no raw counterpart for now and are compared automatically as soon as the raw data holds the values.")
                    info["Rows"][rating_definition["alias"]] = info["Rows"].get(rating_definition["alias"], 0)
                    continue
            raw_rows = build_rating_raw_rows(generator_frame, month_labels, value_columns, name_map, group_assets, rating_definition["group_key"], group_extra_includes, extra_match_case, measure["collections"], measure["column"], rating_measure_factor(measure, unit_factor), measure)
            report_labels, ordered_keys = {}, []
            for report_row in report_rows:
                if report_row["alias"].lower() == rating_definition["alias"].lower() and report_row["name_key"] in raw_rows and report_row["name_key"] not in report_labels:
                    report_labels[report_row["name_key"]] = report_row["label"]
                    ordered_keys.append(report_row["name_key"])
            ordered_keys += sorted(name_key for name_key in raw_rows if name_key not in report_labels)
            for name_key in ordered_keys:
                row_title = report_labels.get(name_key, f"{raw_rows[name_key]['printed']}:{rating_definition['alias']}")
                table_rows.append([row_title] + [float(v) for v in raw_rows[name_key]["values"]])
            info["Rows"][rating_definition["alias"]] = info["Rows"].get(rating_definition["alias"], 0) + len(ordered_keys)
        info["Total Rows"] = len(table_rows)
        if len(table_rows) == 0:
            info["Note"] = "no raw Generator row belongs to the Ratings Report groups: no raw counterpart for this section"
            continue
        section_data = pd.DataFrame(table_rows, columns=list(raw_columns))
        if section_key in raw_ratings_tables:
            raw_ratings_tables[section_key]["data"] = pd.concat([raw_ratings_tables[section_key]["data"], section_data], ignore_index=True)
        else:
            raw_ratings_tables[section_key] = {"title": raw_timeslice_value, "data": section_data}
    return raw_ratings_tables, build_info
def parse_reports_into_sections(reports, in_scope_tables, used_in_model_path, used_in_datamodel_tables, table_order):
    """Parse every report into sections, apply the in-scope and Used in DataModel filters (updates reports and table_order in place).
    Returns all_plexos_section_keys. REPLACES the existing function: the only change is the Ratings message, which says '(no raw counterpart)' only when the Ratings Report really has no raw tables."""
    all_plexos_section_keys = {}
    for report_name, report_config in reports.items():
        plexos_tables, plexos_format_issues, _, _ = parse_plexos_report_sections(
            plexos_rows=report_config["PLEXOS_rows"], report_name=report_name,
            in_scope_tables=in_scope_tables if report_name == "Standard Report" else None)
        all_plexos_section_keys[report_name] = list(plexos_tables.keys())
        raw_count = lambda: len(reports[report_name]["Raw_tables"])
        if report_name == "Standard Report":
            if used_in_model_path != "":
                plexos_dropped = sorted(set(plexos_tables) - used_in_datamodel_tables, key=section_sort_key)
                plexos_tables = filter_tables_by_keys(plexos_tables, used_in_datamodel_tables)
                reports[report_name]["Raw_tables"] = filter_tables_by_keys(reports[report_name]["Raw_tables"], used_in_datamodel_tables)
                all_plexos_section_keys[report_name] = list(plexos_tables.keys())
                table_order[:] = [t for t in table_order if t in used_in_datamodel_tables]
                print(f"[{report_name}] Tables kept (in scope and Used in DataModel): Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
                if plexos_dropped:
                    print(f"[{report_name}] In-scope PLEXOS table(s) dropped (not marked 'Used in DataModel'): {plexos_dropped}")
            else:
                print(f"[{report_name}] 'Used in DataModel' filter skipped -- all in-scope sections kept: Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
        else:
            print(f"[{report_name}] 'Used in DataModel' filter skipped (not applicable to named sections) -- all sections kept: Raw={raw_count()}{' (no raw counterpart)' if raw_count() == 0 else ' (raw counterpart built from the raw data)'}, PLEXOS={len(plexos_tables)}")
            print(f"[{report_name}] PLEXOS section keys found (raw, pre-alias): {sorted(plexos_tables.keys())}")
        report_config["PLEXOS_tables"] = plexos_tables
        report_config["PLEXOS_format_issues"] = plexos_format_issues
    return all_plexos_section_keys
def clean_sit_input_paths(path_names):
    """Strip stray spaces/quotes from the SIT input path variables (kept in the notebook globals) and print each one ('' = skipped)."""
    for path_name in path_names:
        globals()[path_name] = str(globals()[path_name]).strip().strip('"').strip("'")
        print(f"  {path_name}: {globals()[path_name] if globals()[path_name] != '' else '(skipped)'}")
def prepare_results_folder(results_folder):
    """Return the results folder as a Path, creating it when needed."""
    results_folder = Path(results_folder)
    results_folder.mkdir(parents=True, exist_ok=True)
    return results_folder
def apply_timeslice_filter(loaded, frame_name, standard_timeslice):
    """Keep only the standard Timeslice rows of a raw frame (a frame without a Timeslice column is used as it is). Returns the frame."""
    if "Timeslice" in loaded.columns:
        timeslice_text = loaded["Timeslice"].astype(str).str.strip()
        timeslice_keep = timeslice_text.str.lower() == standard_timeslice.lower()
        if timeslice_keep.any():
            print(f"  {frame_name}: Timeslice '{standard_timeslice}' rows used: {int(timeslice_keep.sum())} of {len(loaded)} "
                  f"(other Timeslice values left out: {sorted(set(timeslice_text[~timeslice_keep]))})")
            return loaded[timeslice_keep].reset_index(drop=True)
        print(f"  WARNING: {frame_name} has a Timeslice column but no '{standard_timeslice}' rows (found: {sorted(set(timeslice_text))}); every row is used")
    return loaded.copy()
def convert_month_column(frame, frame_name, excel_serial_min, excel_serial_max):
    """Add 'Month Label' (Mon-YYYY) to the frame, converting only the DISTINCT Month values (dates, date text or Excel date serials).
    Returns the datetime Series aligned to the frame."""
    month_codes, month_uniques = pd.factorize(frame["Month"])
    uniq_dt_list, uniq_label_list, serial_code_idx, bad_values = [], [], [], []
    for code_idx, month_value in enumerate(month_uniques):
        month_ts = pd.NaT
        if isinstance(month_value, (bool, np.bool_)):
            bad_values.append(month_value)
        elif isinstance(month_value, (int, float, np.integer, np.floating)):
            if excel_serial_min <= month_value <= excel_serial_max:
                month_ts = pd.Timestamp("1899-12-30") + pd.Timedelta(days=float(month_value))
                serial_code_idx.append(code_idx)
            else:
                bad_values.append(month_value)
        else:
            try:
                month_ts = pd.Timestamp(pd.to_datetime(month_value))
            except (ValueError, TypeError):
                bad_values.append(month_value)
                month_ts = pd.NaT
        uniq_dt_list.append(month_ts)
        uniq_label_list.append(None if pd.isna(month_ts) else month_ts.strftime("%b-%Y"))
    frame["Month Label"] = np.array(uniq_label_list + [None], dtype=object)[month_codes]
    month_dt = pd.Series(pd.DatetimeIndex(uniq_dt_list + [pd.NaT]).take(month_codes), index=frame.index)
    if serial_code_idx:
        print(f"  {frame_name}: {int(np.isin(month_codes, serial_code_idx).sum())} Month value(s) were Excel date serial numbers and were converted to calendar months")
    if bad_values:
        print(f"  WARNING: {frame_name} has {len(bad_values)} distinct Month value(s) that cannot be read as a month "
              f"(numbers outside {excel_serial_min}-{excel_serial_max} or unreadable text). Sample: {bad_values[:8]}")
    if month_dt.isna().any():
        print(f"  WARNING: {frame_name} has {int(month_dt.isna().sum())} row(s) whose Month could not be read; they get no Month Label and drop out of the monthly columns")
    return month_dt
def load_raw_frames_cached(raw_data_path, standard_timeslice, excel_serial_min, excel_serial_max):
    """Raw Battery / Region / Generator frames with the Timeslice filter and Month labels applied. The parsed sheets (SIT_RAW_CACHE, keyed by file path, size and
    modified time) and the prepared frames are kept in memory, so a re-run does not read the Excel file again. Returns df_bat, df_reg, df_gen, gen_month_dt."""
    raw_file_stat = Path(raw_data_path).stat()
    raw_cache_key = (str(Path(raw_data_path).resolve()), raw_file_stat.st_size, raw_file_stat.st_mtime_ns)
    raw_cache = globals().get("SIT_RAW_CACHE")
    if raw_cache is not None and raw_cache.get("key") == raw_cache_key and all(k in raw_cache for k in ("df_bat", "df_reg", "df_gen")):
        print("  Raw worksheets: reused from this session's cache (file unchanged since it was last read)")
    else:
        with pd.ExcelFile(raw_data_path) as raw_xl:
            raw_cache = {"key": raw_cache_key, "df_bat": raw_xl.parse("Battery"), "df_reg": raw_xl.parse("Region"), "df_gen": raw_xl.parse("Generator")}
        globals()["SIT_RAW_CACHE"] = raw_cache
    frame_specs = [("df_bat (Battery)", "df_bat"), ("df_reg (Region)", "df_reg"), ("df_gen (Generator)", "df_gen")]
    prepared_key = (standard_timeslice, excel_serial_min, excel_serial_max)
    prepared = raw_cache.get("prepared")
    if prepared is not None and prepared.get("key") == prepared_key:
        print("  Raw frames: Timeslice filter and Month labels reused from this session's cache")
        for frame_name, sheet_key in frame_specs:
            print(f"  {frame_name}: shape {prepared[sheet_key].shape}, collections: {sorted(prepared[sheet_key]['Collection'].unique())}")
        return prepared["df_bat"], prepared["df_reg"], prepared["df_gen"], prepared["gen_month_dt"]
    prepared_frames, gen_month_dt = {}, None
    for frame_name, sheet_key in frame_specs:
        frame = apply_timeslice_filter(raw_cache[sheet_key], frame_name, standard_timeslice)
        month_dt = convert_month_column(frame, frame_name, excel_serial_min, excel_serial_max)
        if sheet_key == "df_gen":
            gen_month_dt = month_dt
        prepared_frames[sheet_key] = frame
        print(f"  {frame_name}: shape {frame.shape}, collections: {sorted(frame['Collection'].unique())}")
    raw_cache["prepared"] = {"key": prepared_key, "df_bat": prepared_frames["df_bat"], "df_reg": prepared_frames["df_reg"],
                             "df_gen": prepared_frames["df_gen"], "gen_month_dt": gen_month_dt}
    return prepared_frames["df_bat"], prepared_frames["df_reg"], prepared_frames["df_gen"], gen_month_dt
def warn_stray_month_labels(frames, month_labels):
    """Warn when a frame has Month Labels that are not Generator months (frames = [(frame_name, frame), ...]); they would drop out of the monthly columns."""
    for frame_name, frame in frames:
        stray_labels = sorted(set(frame["Month Label"].dropna()) - set(month_labels))
        if stray_labels:
            print(f"  WARNING: {frame_name} has month(s) that are not in the Generator months and will not appear in the monthly columns: {stray_labels[:12]}")
class CachedTemplate:
    """Stands in for pd.ExcelFile on the cached template sheets: exposes sheet_names and parse(), so load_maptables, load_template_groups,
    load_contract_factors, load_unit_conversion_rules and load_blueprint_standard work unchanged."""
    def __init__(self, cache):
        self.cache = cache
        self.sheet_names = list(cache["maptables"]) + ["Groups", "Contract_factors", "UnitConversion", "Blueprint_std"]
    def parse(self, sheet_name, header=0, dtype=str):
        return (self.cache["maptables"][sheet_name] if sheet_name in self.cache["maptables"] else self.cache[sheet_name]).copy()
def load_template_cached(template_data_path):
    """Template workbook sheets (maptable_, Groups, Contract_factors, UnitConversion, Blueprint_std), kept in memory (SIT_TEMPLATE_CACHE, keyed by file
    path, size and modified time). Returns a CachedTemplate that can be passed to the load_* functions."""
    template_stat = Path(template_data_path).stat()
    template_cache_key = (str(Path(template_data_path).resolve()), template_stat.st_size, template_stat.st_mtime_ns)
    template_cache = globals().get("SIT_TEMPLATE_CACHE")
    if template_cache is not None and template_cache.get("key") == template_cache_key:
        print("  Template sheets: reused from this session's cache (file unchanged since it was last read)")
    else:
        with pd.ExcelFile(template_data_path) as template_xl:
            template_cache = {"key": template_cache_key,
                              "maptables": {sn: template_xl.parse(sn, header=0, dtype=str) for sn in template_xl.sheet_names if sn.lower().startswith("maptable")},
                              "Groups": template_xl.parse("Groups", dtype=str), "Contract_factors": template_xl.parse("Contract_factors", dtype=str),
                              "UnitConversion": template_xl.parse("UnitConversion", dtype=str), "Blueprint_std": template_xl.parse("Blueprint_std", dtype=str)}
        globals()["SIT_TEMPLATE_CACHE"] = template_cache
    return CachedTemplate(template_cache)
def extract_blueprint_sections(blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                               in_scope_tables, class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables,
                               section_special_factor, extra_include_match_case):
    """Rebuild the in-scope Standard Report sections from the raw frames, driven by Blueprint_std (one pass over the Blueprint rows; everything that depends
    only on the frame, collection, group or identifier is cached). Returns (extracted, extracted_display, extracted_names, extracted_raw_ids,
    extracted_idonly, extracted_rate, extracted_derived_keys, cov_df, table_order, out_of_scope_tables, blueprint_titles)."""
    extracted, extracted_display, extracted_names, extracted_raw_ids = {}, {}, {}, {}
    extracted_idonly, extracted_rate, extracted_derived_keys = {}, {}, {}
    coverage_rows, table_order, blueprint_titles = [], [], {}
    out_of_scope_tables, seen_specs = set(), set()
    df_gen = raw_frames["df_gen"]
    parent_cat = df_gen[df_gen["Collection"] == "Generator"].drop_duplicates("Child Name").set_index("Child Name")["Category"].astype(str).str.strip().str.lower()
    raw_parts = {}
    for part_fkey, part_frame in raw_frames.items():
        for part_coll, part_rows in part_frame.groupby("Collection", sort=False):
            raw_parts[(part_fkey, part_coll)] = part_rows
    part_key_cache, group_mask_cache, id_str_cache, id_printed_cache, printed_row_cache, child_factor_cache = {}, {}, {}, {}, {}, {}
    for brow in blueprint.to_dict("records"):
        header = brow["Header"]
        tmatch = re.match(r"^\(\s*(\w+)\s*\)", header)
        tkey = tmatch.group(1).lower() if tmatch else header.lower()
        if tkey not in in_scope_tables:
            out_of_scope_tables.add(tkey)
            continue
        if tkey not in table_order:
            table_order.append(tkey)
            blueprint_titles[tkey] = map_printed_name(header, name_map)
        cls_in, grp_in, prop_in, pattern = brow["Class"], brow["Group"], brow["Property"], brow["Pattern"].lower()
        cls_l, grp_l = cls_in.lower(), grp_in.lower()
        unit_bp = brow["Unit"]
        sign = float(brow["Sign"]) if brow["Sign"] != "" else 1.0
        use_mean = brow["Rate"].strip().lower() in ("true", "1", "yes")
        cov = {"Table": tkey, "Header": header, "Class": cls_in, "Group": grp_in, "Property": prop_in, "Pattern": pattern,
               "Blueprint Unit": unit_bp, "Sign": sign, "Raw DataFrame": "", "Raw Collection": "", "Raw Column": "",
               "Raw Unit": "", "Target Unit": "", "Unit Factor": "", "Raw Rows Used": 0, "Status": "", "Note": ""}
        spec_id = (header, cls_l, grp_l, prop_in, pattern, unit_bp, sign)
        if spec_id in seen_specs:
            cov["Status"] = "DUPLICATE BLUEPRINT ROW - ignored"
            cov["Note"] = "Row is repeated in Blueprint_std; counted once in the normalized raw view"
            coverage_rows.append(cov)
            continue
        seen_specs.add(spec_id)
        if tkey in skip_tables:
            cov["Status"], cov["Note"] = "NO COUNTERPART - custom section", skip_tables[tkey]
            coverage_rows.append(cov)
            continue
        if pattern.startswith("daily"):
            cov["Status"], cov["Note"] = "NO COUNTERPART - daily pattern", "Raw workbook is monthly only"
            coverage_rows.append(cov)
            continue
        eff_cls, eff_prop = cls_l, prop_in
        if (tkey, cls_l, prop_in) in custom_overrides:
            eff_cls, eff_prop, cov["Note"] = custom_overrides[(tkey, cls_l, prop_in)]
        if eff_cls not in class_to_raw:
            cov["Status"], cov["Note"] = "NO COUNTERPART - class not in raw data", f"Class '{cls_in}' is not in the raw workbook"
            coverage_rows.append(cov)
            continue
        fkey, coll, id_col = class_to_raw[eff_cls]
        cov["Raw DataFrame"], cov["Raw Collection"] = fkey, coll
        cats, gk = None, None
        if grp_l not in ("all", ""):
            gk = (cls_l, grp_l)
            if gk not in group_assets:
                gk = ("generator", grp_l)
            if gk not in group_assets:
                cov["Status"], cov["Note"] = "UNKNOWN GROUP", f"Class '{cls_in}' + Group '{grp_in}' is not defined on the Groups sheet"
                coverage_rows.append(cov)
                continue
            cats = group_assets[gk]
        printed_summary, generated = None, ""
        if pattern == "monthly-summary":
            gl = "all" if cats is None else group_label.get((cls_l, grp_l), group_label.get(("generator", grp_l), grp_in))
            generated = f"{cls_in}-{gl}-{prop_in}-Total"
            printed_summary = map_printed_name(generated, name_map)
        derived_components = derived_measures.get((fkey, coll, eff_prop))
        raw_col = None if (eff_cls, eff_prop) in no_raw_notes else property_to_raw_column.get((fkey, coll), {}).get(eff_prop)
        if raw_col is None:
            note_text = no_raw_notes.get((eff_cls, eff_prop), f"No '{eff_prop}' column for {fkey} / {coll}")
            if printed_summary is not None:
                key_only = normalize_text(printed_summary)
                pv_only = pd.DataFrame(np.nan, index=[key_only], columns=month_labels)
                if tkey in extracted:
                    extracted[tkey] = pd.concat([extracted[tkey], pv_only])
                else:
                    extracted[tkey] = pv_only
                    extracted_display[tkey], extracted_names[tkey], extracted_raw_ids[tkey] = {}, {}, set()
                    extracted_idonly[tkey], extracted_rate[tkey] = set(), use_mean
                extracted_raw_ids[tkey].add(generated)
                extracted_display[tkey][key_only] = printed_summary
                extracted_names[tkey][key_only] = generated
                extracted_idonly[tkey].add(key_only)
                cov["Status"], cov["Note"] = "IDENTIFIER ONLY (no raw measure)", note_text + "; row identifier validated, values not derivable"
            else:
                cov["Status"], cov["Note"] = "NO COUNTERPART - no raw measure", note_text
            coverage_rows.append(cov)
            continue
        cov["Raw Column"] = raw_col
        if derived_components:
            cov["Note"] = (cov["Note"] + "; " if cov["Note"] else "") + f"{eff_prop} derived per generator as the sum of: {', '.join(derived_components)}"
        needed_raw_columns = list(derived_components) if derived_components else [raw_col]
        missing_raw_columns = [c for c in needed_raw_columns if c not in raw_frames[fkey].columns]
        if missing_raw_columns:
            cov["Status"] = "NO COUNTERPART - raw column not in the workbook"
            cov["Note"] = (cov["Note"] + "; " if cov["Note"] else "") + f"The raw {fkey} sheet has no column {missing_raw_columns} (columns found: {list(raw_frames[fkey].columns)})"
            print(f"  WARNING: Blueprint row ({header} / {cls_in} / {grp_in} / {prop_in}) reads raw column(s) {missing_raw_columns} that are not on the raw sheet; the row is listed as 'raw column not in the workbook'")
            coverage_rows.append(cov)
            continue
        um = re.search(r"\(([^)]*)\)\s*$", raw_col)
        raw_unit = um.group(1).strip().lower() if um else "-"
        raw_unit = "hours" if raw_unit == "h" else raw_unit
        part = raw_parts.get((fkey, coll))
        if part is None:
            part = raw_frames[fkey].iloc[0:0]
        sub_mask = None
        if cats is not None:
            mask_key = (fkey, coll, gk)
            if mask_key not in group_mask_cache:
                pkey = (fkey, coll)
                if pkey not in part_key_cache:
                    if coll == "Generator.Fuels":
                        kc = part["Parent Name"].map(parent_cat).fillna("")
                        kn = part["Parent Name"].astype(str)
                    else:
                        kc = part["Category"].astype(str).str.strip().str.lower()
                        kn = part["Child Name"].astype(str)
                    part_key_cache[pkey] = (kc, kn.str.replace(r"\s+", " ", regex=True).str.strip())
                key_cat, key_name = part_key_cache[pkey]
                keep_mask = key_cat.isin(cats)
                for rule_cat_l, rule_strings in group_extra_rules.get(gk, []):
                    in_rule_cat = key_cat == rule_cat_l
                    name_hit = pd.Series(False, index=part.index)
                    for rule_string in rule_strings:
                        name_hit = name_hit | key_name.str.contains(re.escape(rule_string), case=extra_include_match_case, na=False)
                    keep_mask = keep_mask | (in_rule_cat & name_hit)
                group_mask_cache[mask_key] = keep_mask
            sub_mask = group_mask_cache[mask_key]
        sub = part if sub_mask is None else part[sub_mask]
        sub_value = sub[derived_components].sum(axis=1, min_count=1) if derived_components else sub[raw_col]
        id_key = (fkey, coll, id_col)
        if id_key not in id_str_cache:
            id_str_all = part[id_col].astype(str)
            id_codes, id_uniques = pd.factorize(id_str_all)
            id_printed_list = [map_printed_name(s, name_map) for s in id_uniques]
            id_key_list = [normalize_text(p) for p in id_printed_list]
            id_str_cache[id_key] = id_str_all
            id_printed_cache[id_key] = dict(zip(id_uniques, id_printed_list))
            printed_row_cache[id_key] = (pd.Series(np.array(id_printed_list, dtype=object)[id_codes], index=part.index),
                                         pd.Series(np.array(id_key_list, dtype=object)[id_codes], index=part.index))
        id_series = id_str_cache[id_key] if sub_mask is None else id_str_cache[id_key][sub_mask]
        uniq_ids = pd.unique(id_series)
        if printed_summary is not None:
            summary_key = normalize_text(printed_summary)
            key_series = pd.Series(summary_key, index=sub.index)
            dedupe = pd.DataFrame({"k": summary_key, "n": printed_summary, "i": uniq_ids})
            hint_src = printed_summary
        else:
            printed_all, key_all = printed_row_cache[id_key]
            key_series = key_all if sub_mask is None else key_all[sub_mask]
            uniq_printed = [id_printed_cache[id_key][s] for s in uniq_ids]
            dedupe = pd.DataFrame({"k": [normalize_text(p) for p in uniq_printed], "n": uniq_printed, "i": uniq_ids})
            hint_src = header
        hm = re.search(r"\(([^()]*)\)\s*$", hint_src.strip())
        target = unit_bp if unit_bp != "" else (hm.group(1).strip() if hm else raw_unit)
        t_l, f_l, thousand = target.lower().strip(), raw_unit, 1.0
        if t_l.startswith("1000·"):
            t_l, thousand = t_l[len("1000·"):], 1.0 / 1000.0
        t_l = "hours" if t_l == "h" else t_l
        if t_l == f_l:
            factor = 1.0 * thousand
        elif (f_l, t_l) in unit_rules:
            factor = unit_rules[(f_l, t_l)] * thousand
        else:
            factor = None
        cov["Raw Unit"], cov["Target Unit"] = raw_unit, target
        if factor is None:
            cov["Status"], cov["Note"] = "NO UNIT RULE", f"UnitConversion has no rule {raw_unit} -> {target}"
            coverage_rows.append(cov)
            continue
        cov["Unit Factor"] = factor * sign
        sub_value = sub_value * factor * sign
        if section_special_factor.get(tkey):
            cf_key = (fkey, coll)
            if cf_key not in child_factor_cache:
                child_codes, child_uniques = pd.factorize(part["Child Name"].astype(str))
                child_factors = np.array([contract_factor.get(normalize_text(s), 1.0) for s in child_uniques], dtype=float)
                child_factor_cache[cf_key] = pd.Series(child_factors[child_codes] if len(child_factors) else np.array([], dtype=float), index=part.index)
            cf_all = child_factor_cache[cf_key]
            sub_value = sub_value * (cf_all if sub_mask is None else cf_all[sub_mask])
        cov["Raw Rows Used"] = int(len(sub))
        work = pd.DataFrame({"Report Key": key_series, "Month Label": sub["Month Label"], "Value": sub_value})
        pv = work.groupby(["Report Key", "Month Label"])["Value"].agg("mean" if use_mean else "sum").dropna().unstack("Month Label").reindex(columns=month_labels)
        disp = dedupe.drop_duplicates("k").set_index("k")["n"].to_dict()
        names = dedupe.groupby("k")["i"].agg(lambda s: " + ".join(sorted(set(str(x) for x in s)))).to_dict()
        ids = {generated} if printed_summary is not None else set(str(x) for x in uniq_ids)
        if tkey in extracted:
            extracted[tkey] = extracted[tkey].add(pv, fill_value=0.0)
            extracted_display[tkey].update({k: v for k, v in disp.items() if k not in extracted_display[tkey]})
            for k, v in names.items():
                extracted_names[tkey][k] = (extracted_names[tkey][k] + " + " + v) if k in extracted_names[tkey] else v
            extracted_raw_ids[tkey] |= ids
        else:
            extracted[tkey] = pv
            extracted_display[tkey] = dict(disp)
            extracted_names[tkey] = names
            extracted_raw_ids[tkey] = set(ids)
            extracted_idonly[tkey] = set()
            extracted_rate[tkey] = use_mean
        if derived_components:
            extracted_derived_keys.setdefault(tkey, set()).update(pv.index)
        cov["Status"] = "EXTRACTED" if not derived_components else "EXTRACTED (derived measure)"
        coverage_rows.append(cov)
    table_order.sort(key=section_sort_key)
    scope_missing_from_blueprint = [t for t in in_scope_tables if t not in table_order]
    print(f"  Scope: {len(in_scope_tables)} Standard sections in scope; {len(out_of_scope_tables)} Blueprint_std sections outside the scope were excluded")
    if scope_missing_from_blueprint:
        print(f"  WARNING: in-scope section(s) not found in Blueprint_std: {scope_missing_from_blueprint}")
    cov_df = pd.DataFrame(coverage_rows)
    if not cov_df.empty:
        print(f"  Blueprint_std: {len(cov_df)} rows, {len(table_order)} sections; raw measure found for "
              f"{int(cov_df['Status'].str.startswith('EXTRACTED').sum())} rows (of which derived: {int((cov_df['Status'] == 'EXTRACTED (derived measure)').sum())}), "
              f"identifier-only {int((cov_df['Status'] == 'IDENTIFIER ONLY (no raw measure)').sum())}, "
              f"duplicate rows ignored {int((cov_df['Status'] == 'DUPLICATE BLUEPRINT ROW - ignored').sum())}")
    return (extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys,
            cov_df, table_order, out_of_scope_tables, blueprint_titles)
def get_reports_without_raw(reports):
    """Names of the reports that have no raw counterpart (no raw tables)."""
    return [report_name for report_name, report_config in reports.items() if len(report_config["Raw_tables"]) == 0]
def get_ordered_section_keys(report_name, raw_tables, px_tables, table_order):
    """Section keys of a report: Standard = Blueprint order sections plus any other section found, in section order; Ratings = sorted by name."""
    if report_name == "Standard Report":
        return sorted(set(table_order) | set(raw_tables) | set(px_tables), key=section_sort_key)
    return sorted(set(raw_tables) | set(px_tables), key=str)
def summarize_row_titles(data):
    """Row titles of a section table (first column, blanks dropped). Returns the titles, a Counter of the normalized titles and {normalized title: first display text}."""
    titles = [] if data.empty or data.shape[1] == 0 else data.iloc[:, 0].fillna("").astype(str).str.strip().tolist()
    titles = [t for t in titles if t != ""]
    keys = [normalize_text(t) for t in titles]
    display = {}
    for key, text in zip(keys, titles):
        display.setdefault(key, text)
    return titles, Counter(keys), display
def build_row_exception_record(step_label, report_name, table_number, raw_title, px_title, row_title, raw_names, raw_occurrences, px_occurrences,
                               identical, missing, extra, difference_type):
    """One exception-report row (a row title missing from PLEXOS, extra in PLEXOS, or with a different occurrence count)."""
    return {"PlexOS Step": step_label, "Report": report_name, "Table Number": table_number, "Raw (Section-Mapping) Title": raw_title, "PLEXOS Title": px_title,
            "Row Title": row_title, "Raw Data Name(s)": raw_names, "Raw Occurrences": raw_occurrences, "PLEXOS Occurrences": px_occurrences,
            "Identical Occurrences": identical, "Missing from PLEXOS": missing, "Extra in PLEXOS": extra, "Difference Type": difference_type, "Status": "FAIL"}
def build_row_comparison_record(step_label, report_name, table_number, raw_title, px_title, raw_present, px_present, raw_row_count, px_row_count,
                                identical, missing, extra, distinct_compared, occurrence_match, titles_match, status, note):
    """One row-comparison-report row (one per report section)."""
    return {"PlexOS Step": step_label, "Report": report_name, "Table Number": table_number, "Raw (Section-Mapping) Title": raw_title, "PLEXOS Title": px_title,
            "Raw Present": raw_present, "PLEXOS Present": px_present, "Raw Row Count": raw_row_count, "PLEXOS Row Count": px_row_count,
            "Identical Row Title Count": identical, "Missing from PLEXOS Count": missing, "Extra in PLEXOS Count": extra,
            "Distinct Row Titles Compared": distinct_compared, "Occurrence Counts Match": occurrence_match, "Row Titles Match": titles_match,
            "Status": status, "Note": note}
def compare_row_presence(reports, table_order, blueprint_titles, extracted_names, no_counterpart, ratings_no_raw_reason, step_label="PlexOS-3.03B"):
    """Compare the row titles of every report section between the raw and PLEXOS sides in one pass.
    Returns row_comparison_results, row_exception_results, shared_sections_expected_total, sections_compared_total."""
    exception_columns = ["PlexOS Step", "Report", "Table Number", "Raw (Section-Mapping) Title", "PLEXOS Title", "Row Title", "Raw Data Name(s)",
                         "Raw Occurrences", "PLEXOS Occurrences", "Identical Occurrences", "Missing from PLEXOS", "Extra in PLEXOS", "Difference Type", "Status"]
    comparison_columns = ["PlexOS Step", "Report", "Table Number", "Raw (Section-Mapping) Title", "PLEXOS Title", "Raw Present", "PLEXOS Present",
                          "Raw Row Count", "PLEXOS Row Count", "Identical Row Title Count", "Missing from PLEXOS Count", "Extra in PLEXOS Count",
                          "Distinct Row Titles Compared", "Occurrence Counts Match", "Row Titles Match", "Status", "Note"]
    comparison_rows, exception_rows = [], []
    shared_expected_total, sections_compared_total = 0, 0
    for report_name, report_config in reports.items():
        raw_tables, px_tables = report_config["Raw_tables"], report_config["PLEXOS_tables"]
        ordered_keys = get_ordered_section_keys(report_name, raw_tables, px_tables, table_order)
        shared_expected_total += len([k for k in ordered_keys if k in raw_tables and k in px_tables])
        for table_number in ordered_keys:
            raw_entry, px_entry = raw_tables.get(table_number), px_tables.get(table_number)
            raw_present, px_present = raw_entry is not None, px_entry is not None
            in_blueprint = (report_name == "Standard Report") and (table_number in table_order)
            raw_title = raw_entry["title"] if raw_present else (blueprint_titles.get(table_number, "") if in_blueprint else "")
            px_title = px_entry["title"] if px_present else ""
            raw_name_lookup = extracted_names.get(table_number, {}) if report_name == "Standard Report" else {}
            if not (raw_present and px_present):
                if raw_present and not px_present:
                    section_status, note = "FAIL", "mapped section is missing from the PLEXOS output (all raw rows are missing)"
                elif in_blueprint and not px_present:
                    section_status, note = "FAIL", "section is in the section-mapping table but missing from the PLEXOS output"
                else:
                    section_status = "N/A - " + no_counterpart
                    note = ratings_no_raw_reason if report_name == "Ratings Report" else "Section has no raw counterpart (no raw measure for it in the raw data)"
                raw_row_total = len(raw_entry["data"]) if raw_present else 0
                if raw_present and raw_row_total > 0:
                    for row_title_value in raw_entry["data"].iloc[:, 0].tolist():
                        row_title_text = str(row_title_value).strip()
                        exception_rows.append(build_row_exception_record(step_label, report_name, table_number, raw_title, px_title, row_title_text,
                                                                         raw_name_lookup.get(normalize_text(row_title_text), ""), 1, 0, 0, 1, 0, "MISSING FROM PLEXOS"))
                match_value = False if section_status == "FAIL" else ""
                comparison_rows.append(build_row_comparison_record(step_label, report_name, table_number, raw_title, px_title, raw_present, px_present,
                                                                   raw_row_total, 0 if not px_present else len(px_entry["data"]), 0, raw_row_total, 0, 0,
                                                                   match_value, match_value, section_status, note))
                continue
            raw_titles_display, raw_counts, raw_display = summarize_row_titles(raw_entry["data"])
            px_titles_display, px_counts, px_display = summarize_row_titles(px_entry["data"])
            identical_total = missing_total = extra_total = 0
            distinct_titles = sorted(set(raw_counts) | set(px_counts))
            for key in distinct_titles:
                raw_count, px_count = raw_counts.get(key, 0), px_counts.get(key, 0)
                identical_occurrences = min(raw_count, px_count)
                missing_count, extra_count = max(raw_count - px_count, 0), max(px_count - raw_count, 0)
                identical_total += identical_occurrences
                missing_total += missing_count
                extra_total += extra_count
                if missing_count > 0 or extra_count > 0:
                    if raw_count > 0 and px_count == 0:
                        difference_type = "MISSING FROM PLEXOS"
                    elif px_count > 0 and raw_count == 0:
                        difference_type = "EXTRA IN PLEXOS"
                    else:
                        difference_type = "OCCURRENCE COUNT MISMATCH"
                    exception_rows.append(build_row_exception_record(step_label, report_name, table_number, raw_title, px_title,
                                                                     px_display.get(key, raw_display.get(key, key)), raw_name_lookup.get(key, ""),
                                                                     raw_count, px_count, identical_occurrences, missing_count, extra_count, difference_type))
            row_titles_match = (missing_total == 0 and extra_total == 0)
            occurrence_counts_match = all(raw_counts.get(k, 0) == px_counts.get(k, 0) for k in distinct_titles)
            all_match = row_titles_match and occurrence_counts_match
            comparison_rows.append(build_row_comparison_record(step_label, report_name, table_number, raw_title, px_title, True, True,
                                                               len(raw_titles_display), len(px_titles_display), identical_total, missing_total, extra_total,
                                                               len(distinct_titles), occurrence_counts_match, row_titles_match, "PASS" if all_match else "FAIL",
                                                               "" if all_match else f"{missing_total} missing, {extra_total} extra"))
            sections_compared_total += 1
    return (pd.DataFrame(comparison_rows, columns=comparison_columns), pd.DataFrame(exception_rows, columns=exception_columns),
            shared_expected_total, sections_compared_total)
def split_row_comparison_results(row_comparison_results):
    """Split the row-comparison report. Returns compared_sections (present on both sides, match columns as real booleans), unmapped_sections
    (N/A: no raw counterpart) and section_level_misses (FAIL sections missing from PLEXOS)."""
    both_sides = row_comparison_results["Raw Present"].astype(bool) & row_comparison_results["PLEXOS Present"].astype(bool)
    compared_sections = row_comparison_results[both_sides].copy()
    for bool_col in ("Row Titles Match", "Occurrence Counts Match"):
        compared_sections[bool_col] = compared_sections[bool_col].astype(bool)
    unmapped_sections = row_comparison_results[row_comparison_results["Status"].astype(str).str.startswith("N/A")]
    section_level_misses = row_comparison_results[(row_comparison_results["Status"] == "FAIL") & ~row_comparison_results["PLEXOS Present"].astype(bool)]
    return compared_sections, unmapped_sections, section_level_misses
def print_exception_step(exception_rows, heading, count_column, total_phrase, line_formatter, empty_message, show_more=True, max_lines=15):
    """Print an exception-type step (heading, per-table counts, the first rows, optional '... and N more'). Returns True when there are no exceptions."""
    print(heading)
    if exception_rows.empty:
        print(f"  {empty_message}")
        return True
    summary = exception_rows.groupby(["Report", "Table Number"]).size().reset_index(name=count_column)
    print(summary.to_string(index=False))
    if total_phrase:
        print(f"  ({len(exception_rows)} row(s) {total_phrase} across {len(summary)} table(s) -- row-level detail is in the exception report)")
    for _, r in exception_rows.head(max_lines).iterrows():
        print(f"    {line_formatter(r)}")
    if show_more and len(exception_rows) > max_lines:
        print(f"    ... and {len(exception_rows) - max_lines} more")
    return False
def column_total(results_df, column_name):
    """Integer sum of a results column (0 for an empty table)."""
    return int(results_df[column_name].sum()) if not results_df.empty else 0
def verify_results_csv(output_path, expected_rows, required_columns, expected_reports):
    """Read a written results CSV back. Returns file_ok, rows_ok, columns_ok, reports_ok."""
    if not Path(output_path).is_file():
        return False, False, False, False
    readback = pd.read_csv(output_path)
    return True, len(readback) == expected_rows, all(c in readback.columns for c in required_columns), set(readback["Report"]) == set(expected_reports)
def verify_exception_csv(output_path, expected_rows):
    """Read a written exception CSV back. Returns file_ok, count_ok (every exception written), identified_ok (report type and section on every row)."""
    if not Path(output_path).is_file():
        return False, False, False
    try:
        readback = pd.read_csv(output_path)
    except pd.errors.EmptyDataError:
        return True, expected_rows == 0, True
    return True, len(readback) == expected_rows, bool(readback.empty or (readback["Report"].notna().all() and readback["Table Number"].notna().all()))
def print_simultaneous_execution(results_df, reports, reports_without_raw, no_counterpart, ratings_no_raw_reason):
    """Print how many sections each report evaluated in the same run. Returns True when both the Standard and the Ratings report were evaluated."""
    for report_name in reports:
        suffix = f" (all listed as '{no_counterpart}': {ratings_no_raw_reason})" if report_name in reports_without_raw else ""
        print(f"  {report_name}: {len(filter_report_rows(results_df, report_name))} section(s) evaluated in the same run{suffix}")
    return set(results_df["Report"]) == {"Standard Report", "Ratings Report"}

################################################################################################################################################################################
#3.03C
################################################################################################################################################################################
def build_rating_raw_name_lookup(rating_frames, rating_definitions, rating_sections, value_columns, month_labels, name_map, group_assets, group_extra_includes, extra_match_case, unit_factor, section_aliases):
    """The raw unit names behind every raw row of the Ratings Report counterpart (build_raw_ratings_tables), so the column 'Raw Data Name(s)' of the results can say which raw units a Ratings row was built from, like the Standard Report rows do. Returns {Ratings section key: {normalized row title: 'raw name + raw name'}}. The row title is the label the Ratings Report prints for the unit (spaces collapsed; '<printed name>:<alias>' when the report has no such row), exactly as in the raw table, and the key is normalize_text(title), the same key index_row_positions gives the section tables. A Timeslice whose proof failed is skipped (it has no raw table). Only the names are collected here; the values are the ones of build_raw_ratings_tables."""
    name_lookup = {}
    for raw_timeslice_value, (generator_frame, timeslice_proven, proof_text) in rating_frames.items():
        if not timeslice_proven:
            continue
        section_key = rating_timeslice_key(raw_timeslice_value, section_aliases)
        report_rows = rating_sections.get(section_key, {}).get("rows", [])
        section_names = name_lookup.setdefault(section_key, {})
        for rating_definition in rating_definitions:
            measure = rating_definition["measure"]
            if not rating_definition_active(rating_definition, report_rows):
                continue
            raw_rows = build_rating_raw_rows(generator_frame, month_labels, value_columns, name_map, group_assets, rating_definition["group_key"], group_extra_includes, extra_match_case, measure["collections"], measure["column"], rating_measure_factor(measure, unit_factor), measure)
            report_labels = {}
            for report_row in report_rows:
                if report_row["alias"].lower() == rating_definition["alias"].lower() and report_row["name_key"] in raw_rows and report_row["name_key"] not in report_labels:
                    report_labels[report_row["name_key"]] = report_row["label"]
            for name_key, raw_row in raw_rows.items():
                row_title = report_labels.get(name_key, f"{raw_row['printed']}:{rating_definition['alias']}")
                section_names[normalize_text(row_title)] = " + ".join(raw_row["raw_names"])
    return name_lookup
def make_report_headers_unique(reports):
    """Rename duplicate column headers in every parsed table of every report (in place). Returns the number of tables changed."""
    tables_changed = 0
    for report_name, report_data in reports.items():
        for tables_key in ("PLEXOS_tables", "Raw_tables"):
            for table_number, table in (report_data.get(tables_key) or {}).items():
                frame = table["data"] if isinstance(table, dict) and "data" in table else table
                if not hasattr(frame, "columns") or not frame.columns.duplicated().any():
                    continue
                seen_headers, unique_headers = {}, []
                for header in frame.columns:
                    if header in seen_headers:
                        seen_headers[header] += 1
                        unique_headers.append(f"{header}.{seen_headers[header]}")
                    else:
                        seen_headers[header] = 0
                        unique_headers.append(header)
                frame.columns = unique_headers
                tables_changed += 1
    return tables_changed
def canonical_header(header):
    """Turn many header spellings into the layout names: Jan-2026, Tot-2026, Total."""
    text = str(header).strip()
    low = re.sub(r"\s+", " ", text.lower().replace("_", " "))
    found = px_month_text_re.match(low)
    if found:
        year_number = int(found.group(2))
        if year_number < 100:
            year_number += 2000
        return f"{found.group(1).title()}-{year_number}"
    found = px_iso_date_re.match(low)
    if found:
        month_number = int(found.group(2))
        if 1 <= month_number <= 12:
            return f"{MONTH_ABBR_BY_NUMBER[month_number]}-{found.group(1)}"
    found = px_total_year_a_re.match(low)
    if found is None:
        found = px_total_year_b_re.match(low)
    if found:
        return f"Tot-{found.group(1)}"
    if low in ("total", "grand total", "tot"):
        return "Total"
    return text
def normalize_plexos_headers(reports, expected_columns):
    """Standard Report PLEXOS tables: rename header spellings to the layout names; when names still do not match but the column count is exact, assign the expected names by position."""
    renamed_tables, positional_tables = 0, 0
    for table_number, table in (reports["Standard Report"].get("PLEXOS_tables") or {}).items():
        frame = table["data"]
        old_headers = [str(c) for c in frame.columns]
        new_headers = [old_headers[0]] + [canonical_header(c) for c in old_headers[1:]]
        if len([c for c in expected_columns[1:] if c not in set(new_headers[1:])]) > 0 and len(new_headers) == len(expected_columns):
            new_headers = [old_headers[0]] + list(expected_columns[1:])
            positional_tables += 1
        seen_headers = {}
        unique_headers = []
        for header in new_headers:
            if header in seen_headers:
                seen_headers[header] += 1
                unique_headers.append(f"{header}.{seen_headers[header]}")
            else:
                seen_headers[header] = 0
                unique_headers.append(header)
        if not (unique_headers == old_headers):
            frame.columns = unique_headers
            renamed_tables += 1
    return renamed_tables, positional_tables
def build_raw_column_layout(gen_month_dt):
    """Normalized raw layout from the Generator month datetimes (two dates in the same month give ONE label). Returns month_labels, raw_years, raw_columns, expected_monthly_columns. REPLACES the existing function."""
    month_labels = list(dict.fromkeys(gen_month_dt.dropna().drop_duplicates().sort_values().dt.strftime("%b-%Y").tolist()))
    raw_years = sorted(set(int(m[-4:]) for m in month_labels))
    raw_columns = [""]
    for yr in raw_years:
        raw_columns.extend(m for m in month_labels if m.endswith(str(yr)))
        raw_columns.append(f"Tot-{yr}")
    raw_columns.append("Total")
    expected_monthly_columns = len(month_labels) + len(raw_years) + 1
    print(f"  Normalized raw layout: {len(month_labels)} months + {len(raw_years)} Tot-YYYY + 1 Total = {expected_monthly_columns} columns")
    return month_labels, raw_years, raw_columns, expected_monthly_columns
def apply_timeslice_filter(loaded, frame_name, standard_timeslice):
    """Keep only the standard Timeslice rows of a raw frame. The column is found whatever its capitalization / spacing ('Timeslice', 'TimeSlice', 'Time Slice'); a frame without one is used as it is, with a loud warning. REPLACES the existing function."""
    timeslice_column = find_normalized_column(loaded, "timeslice")
    if timeslice_column is None:
        print(f"  WARNING: {frame_name} has no Timeslice column (columns: {list(loaded.columns)[:12]}); every row is used. If the sheet holds All Periods + Off-Peak + On-Peak rows, the values are counted more than once -- see the duplicate-row check below")
        return loaded.copy()
    timeslice_text = loaded[timeslice_column].astype(str).str.strip()
    timeslice_keep = timeslice_text.str.lower() == standard_timeslice.lower()
    if timeslice_keep.any():
        print(f"  {frame_name}: Timeslice column '{timeslice_column}': '{standard_timeslice}' rows used: {int(timeslice_keep.sum())} of {len(loaded)} (other Timeslice values left out: {sorted(set(timeslice_text[~timeslice_keep]))})")
        return loaded[timeslice_keep].reset_index(drop=True)
    print(f"  WARNING: {frame_name} has a Timeslice column '{timeslice_column}' but no '{standard_timeslice}' rows (found: {sorted(set(timeslice_text))}); every row is used")
    return loaded.copy()
def verify_exception_csv(output_path, expected_rows, difference_types=None):
    """Read a written exception CSV back. Returns file_ok, count_ok (every exception written), identified_ok (report type and section on every row, and every Difference Type in difference_types when given). REPLACES the existing function."""
    if not Path(output_path).is_file():
        return False, False, False
    try:
        readback = pd.read_csv(output_path)
    except pd.errors.EmptyDataError:
        return True, expected_rows == 0, True
    identified_ok = bool(readback.empty or (readback["Report"].notna().all() and readback["Table Number"].notna().all() and (difference_types is None or readback["Difference Type"].isin(difference_types).all())))
    return True, len(readback) == expected_rows, identified_ok
def find_raw_duplicate_rows(frames, results_folder, file_name):
    """One raw row per resource-month: after the Timeslice filter no resource-month may appear twice (a repeat is added up twice). frames = [(frame_name, frame), ...]. Prints warnings, saves up to 5000 rows and returns the duplicate rows."""
    raw_duplicate_parts = []
    for frame_name, frame in frames:
        duplicate_key_columns = [c for c in ("Collection", "Parent Name", "Child Name", "Month Label") if c in frame.columns]
        usable_frame = frame[frame["Month Label"].notna()]
        duplicate_mask = usable_frame.duplicated(subset=duplicate_key_columns, keep=False)
        if duplicate_mask.any():
            duplicate_part = usable_frame[duplicate_mask].copy()
            duplicate_part.insert(0, "Raw Sheet", frame_name)
            raw_duplicate_parts.append(duplicate_part)
            print(f"  WARNING: {frame_name}: {int(duplicate_mask.sum())} row(s) share a Collection / Parent / Child / Month with another row; their values are added up together (counted more than once)")
    raw_duplicate_rows = pd.concat(raw_duplicate_parts, ignore_index=True) if raw_duplicate_parts else pd.DataFrame(columns=["Raw Sheet"])
    save_results_csv(raw_duplicate_rows.head(5000), results_folder, file_name)
    print(f"  Raw resource-month rows counted more than once: {len(raw_duplicate_rows)} ({file_name})")
    return raw_duplicate_rows
def split_frames_by_collection(raw_frames):
    """{(frame key, collection): that frame's rows for the collection} (original row order and index kept)."""
    raw_parts = {}
    for part_fkey, part_frame in raw_frames.items():
        for part_coll, part_rows in part_frame.groupby("Collection", sort=False):
            raw_parts[(part_fkey, part_coll)] = part_rows
    return raw_parts
def build_table3_primary_values(plexos_rows, table_present, month_labels):
    """Table 3 (Thermal Unit Fuel Use): rebuild each generator's PLEXOS series as (Primary) + (Secondary) + (Topping), read straight from the Standard Report rows. Returns {generator: [one array per occurrence]}; unreadable cells are counted and reported."""
    table3_px_values = {}
    table3_unreadable_cells = 0
    if table_present:
        section_header_re = re.compile(r"^\(\s*\d+[a-zA-Z]?\s*\)")
        section_3_re = re.compile(r"^\(\s*3\s*\)")
        month_header_re = re.compile(r"^[A-Za-z]{3}-\d{4}$")
        n_months_t3 = len(month_labels)
        in_section_3, header_3, header_3_positions, current_generator = False, None, None, None
        for r in plexos_rows:
            stripped = [str(c).strip() for c in r]
            non_blank = [c for c in stripped if c]
            if not non_blank:
                continue
            row_text_t3 = " ".join(non_blank)
            if section_header_re.match(row_text_t3):
                in_section_3, header_3, header_3_positions, current_generator = bool(section_3_re.match(row_text_t3)), None, None, None
                continue
            if not in_section_3:
                continue
            if header_3 is None:
                if any(month_header_re.match(c) for c in stripped):
                    header_3 = {}
                    for cell_index, cell_text in enumerate(stripped):
                        if cell_text != "" and cell_text not in header_3:
                            header_3[cell_text] = cell_index
                    header_3_positions = [header_3.get(col) for col in month_labels]
                continue
            label = normalize_text(stripped[0])
            if label == "":
                continue
            if label == "total":
                current_generator = None
                continue
            if label.startswith("("):
                if current_generator is not None and label in ("(primary)", "(secondary)", "(topping)"):
                    values = np.zeros(n_months_t3)
                    for position_index, cell_position in enumerate(header_3_positions):
                        if cell_position is not None and cell_position < len(r):
                            cell_clean = str(r[cell_position]).replace(",", "").replace("$", "").replace("%", "").strip()
                            if cell_clean == "":
                                continue
                            try:
                                values[position_index] = float(cell_clean)
                            except ValueError:
                                table3_unreadable_cells += 1
                    table3_px_values[current_generator][-1] = table3_px_values[current_generator][-1] + values
            else:
                current_generator = label
                table3_px_values.setdefault(current_generator, []).append(np.zeros(n_months_t3))
    print(f"Table 3 PLEXOS rebuild (Primary + Secondary + Topping) prepared for {len(table3_px_values)} generator(s)")
    if table3_unreadable_cells > 0:
        print(f"  WARNING: {table3_unreadable_cells} Table 3 cell(s) could not be read as numbers and were counted as 0.0")
    if table_present and len(table3_px_values) == 0:
        print("  WARNING: no Table 3 generator rows were read straight from the Standard Report; Table 3 falls back to the ordinary row totals (which include start-up fuel)")
    return table3_px_values
def to_numeric_matrix(frame_part):
    """Cell-by-cell text -> number conversion of a block of values (removes ',' '$' '%'; unreadable = NaN), reshaped back to the block's shape."""
    return pd.to_numeric(pd.Series(frame_part.to_numpy().ravel()).astype(str).str.replace(",", "", regex=False).str.replace("$", "", regex=False).str.replace("%", "", regex=False), errors="coerce").to_numpy(dtype=float).reshape(frame_part.shape)
def index_row_positions(data):
    """Row-title index of a section table. Returns positions {normalized title: [row positions]} and display {normalized title: first title text} (blank titles skipped)."""
    labels = data.iloc[:, 0].fillna("").astype(str).str.strip() if data.shape[1] > 0 else pd.Series([], dtype=str)
    positions, display = {}, {}
    for position, text in enumerate(labels.tolist()):
        if text == "":
            continue
        key = normalize_text(text)
        positions.setdefault(key, []).append(position)
        display.setdefault(key, text)
    return positions, display
def build_missing_section_records(step_label, report_name, table_number, table_title, raw_entry, px_entry, in_blueprint, raw_name_lookup, no_counterpart, ratings_no_raw_reason):
    """Records for a section that is not on both sides: either 'N/A - no counterpart' or a FAIL (mapped section missing from the PLEXOS output, every raw row then missing). Returns presence_row, exception_rows."""
    raw_present, px_present = raw_entry is not None, px_entry is not None
    if raw_present or in_blueprint:
        section_status = "FAIL"
        note = "mapped section is missing from the PLEXOS output" if raw_present else "section is in the section-mapping table but missing from the PLEXOS output"
    else:
        section_status = "N/A - " + no_counterpart
        note = ratings_no_raw_reason if report_name == "Ratings Report" else "Section has no raw counterpart (no raw measure for it in the raw data)"
    raw_row_total = 0
    exception_rows = []
    if raw_present:
        raw_only_df = raw_entry["data"]
        raw_row_total = len(raw_only_df)
        raw_title_values = raw_only_df.iloc[:, 0].tolist() if raw_row_total > 0 else []
        for row_title_value in raw_title_values:
            row_title_text = str(row_title_value).strip()
            exception_rows.append({"PlexOS Step": step_label, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Row Title": row_title_text,
                                   "Raw Data Name(s)": raw_name_lookup.get(normalize_text(row_title_text), ""), "Raw Occurrences": 1, "PLEXOS Occurrences": 0, "Difference Type": "Missing from Output", "Status": "FAIL"})
    presence_row = {"PlexOS Step": step_label, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Present": raw_present, "PLEXOS Present": px_present,
                    "Raw Row Count": raw_row_total, "PLEXOS Row Count": len(px_entry["data"]) if px_present else 0, "Identical Row Title Count": 0, "Missing from Output Count": raw_row_total,
                    "Extra in Output Count": 0, "Occurrence Counts Match": False if section_status == "FAIL" else "", "Row Titles Match": False if section_status == "FAIL" else "",
                    "Section Status": section_status, "Note": note}
    return presence_row, exception_rows
def compare_section_row_presence(step_label, report_name, table_number, table_title, raw_positions, px_positions, raw_display, px_display, raw_name_lookup):
    """Row-presence comparison of one section present on both sides (identical / missing / extra row titles and occurrence counts). Returns presence_row, exception_rows."""
    identical_total = missing_total = extra_total = 0
    exception_rows = []
    distinct_titles = sorted(set(raw_positions) | set(px_positions))
    for key in distinct_titles:
        raw_count = len(raw_positions.get(key, []))
        px_count = len(px_positions.get(key, []))
        identical_total += min(raw_count, px_count)
        missing_count = max(raw_count - px_count, 0)
        extra_count = max(px_count - raw_count, 0)
        missing_total += missing_count
        extra_total += extra_count
        if missing_count > 0 or extra_count > 0:
            if raw_count > 0 and px_count == 0:
                difference_type = "Missing from Output"
            elif px_count > 0 and raw_count == 0:
                difference_type = "Extra in Output"
            else:
                difference_type = "Occurrence Count Mismatch"
            exception_rows.append({"PlexOS Step": step_label, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Row Title": px_display.get(key, raw_display.get(key, key)),
                                   "Raw Data Name(s)": raw_name_lookup.get(key, ""), "Raw Occurrences": raw_count, "PLEXOS Occurrences": px_count, "Difference Type": difference_type, "Status": "FAIL"})
    titles_match = (missing_total == 0 and extra_total == 0)
    occurrence_match = all(len(raw_positions.get(k, [])) == len(px_positions.get(k, [])) for k in distinct_titles)
    presence_row = {"PlexOS Step": step_label, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Present": True, "PLEXOS Present": True,
                    "Raw Row Count": sum(len(v) for v in raw_positions.values()), "PLEXOS Row Count": sum(len(v) for v in px_positions.values()), "Identical Row Title Count": identical_total,
                    "Missing from Output Count": missing_total, "Extra in Output Count": extra_total, "Occurrence Counts Match": occurrence_match, "Row Titles Match": titles_match,
                    "Section Status": "PASS" if (titles_match and occurrence_match) else "FAIL", "Note": "" if (titles_match and occurrence_match) else f"{missing_total} missing, {extra_total} extra"}
    return presence_row, exception_rows
def build_matched_matrices(raw_df, px_df, monthly_columns, raw_positions, px_positions, common_keys):
    """Numeric matrices (rows x monthly columns) of ONLY the rows matched on both sides, each side from its own table. Returns raw_matrix, px_matrix, raw_row_of, px_row_of ({table row position: matrix row})."""
    raw_needed = sorted({position for k in common_keys for position in raw_positions[k][:len(px_positions[k])]})
    px_needed = sorted({position for k in common_keys for position in px_positions[k][:len(raw_positions[k])]})
    raw_matrix = to_numeric_matrix(raw_df[monthly_columns].iloc[raw_needed])
    px_matrix = to_numeric_matrix(px_df[monthly_columns].iloc[px_needed])
    return raw_matrix, px_matrix, {position: index for index, position in enumerate(raw_needed)}, {position: index for index, position in enumerate(px_needed)}
def summarize_series(series_full):
    """Readable-value count and (minimum, maximum, mean, median) of a monthly series (blank cells dropped). Returns count, stats."""
    finite_values = series_full[~np.isnan(series_full)]
    count = int(finite_values.size)
    if count == 0:
        return 0, (np.nan, np.nan, np.nan, np.nan)
    return count, (finite_values.min(), finite_values.max(), finite_values.sum() / count, np.median(finite_values))
def classify_magnitude(raw_value, px_value, zero_threshold):
    """Power-of-ten test of one statistic (baseline = raw): same floor(log10(abs(value))); zero matches only zero; both empty is consistent; one side empty is a divergence. Returns stat_match (1 / 0), stat_bucket (raw value's power of ten, 'Zero' or 'No Data')."""
    if pd.isna(raw_value) and pd.isna(px_value):
        stat_match = 1
    elif pd.isna(raw_value) or pd.isna(px_value):
        stat_match = 0
    elif abs(raw_value) < zero_threshold and abs(px_value) < zero_threshold:
        stat_match = 1
    elif abs(raw_value) < zero_threshold or abs(px_value) < zero_threshold:
        stat_match = 0
    else:
        stat_match = 1 if math.floor(math.log10(abs(raw_value))) == math.floor(math.log10(abs(px_value))) else 0
    if pd.isna(raw_value):
        stat_bucket = "No Data"
    elif abs(raw_value) < zero_threshold:
        stat_bucket = "Zero"
    else:
        stat_bucket = f"10^{math.floor(math.log10(abs(raw_value)))}"
    return stat_match, stat_bucket
def compute_magnitude_row(raw_stats, px_stats, magnitude_stats, zero_threshold):
    """Result columns of one matched row occurrence: raw / PLEXOS statistic (5 significant figures), match, bucket, and the Raw / PLEXOS mean ratio. Returns fields, all_stats_match."""
    fields = {}
    all_stats_match = True
    for stat_name, raw_value, px_value in zip(magnitude_stats, raw_stats, px_stats):
        stat_match, stat_bucket = classify_magnitude(raw_value, px_value, zero_threshold)
        fields[f"Raw {stat_name}"] = float(f"{raw_value:.5g}") if not pd.isna(raw_value) else np.nan
        fields[f"PLEXOS {stat_name}"] = float(f"{px_value:.5g}") if not pd.isna(px_value) else np.nan
        fields[f"{stat_name} Match"] = stat_match
        fields[f"{stat_name} Magnitude Bucket"] = stat_bucket
        if stat_match == 0:
            all_stats_match = False
    ratio_raw_mean, ratio_px_mean = raw_stats[2], px_stats[2]
    fields["Mean Ratio (Raw / PLEXOS)"] = float(f"{ratio_raw_mean / ratio_px_mean:.5g}") if (not pd.isna(ratio_raw_mean) and not pd.isna(ratio_px_mean) and abs(ratio_px_mean) >= zero_threshold) else np.nan
    return fields, all_stats_match
def rounding_allowance_per_month(sources, rounding_step):
    """Rounding noise of the raw workbook (2 decimals) in report units for one raw name and month: rounding_step x the largest (unit factor x number of components) of the table's raw measures."""
    return rounding_step * (max(abs(s["factor"]) * s["rounding_units"] for s in sources) if sources else 0.0)
def calculate_series_check(raw_series_full, px_series_full, rounding_allowance, zero_threshold, series_rel_tol):
    """Monthly-series check: a month differs when |raw - PLEXOS| (after the raw rounding allowance) is more than series_rel_tol of the row's level. Returns max difference (% of row level), months differing, 'AGREE' / 'DIFFER'."""
    raw_filled = np.nan_to_num(np.asarray(raw_series_full, dtype=float))
    px_filled = np.nan_to_num(np.asarray(px_series_full, dtype=float))
    series_level = max(float(np.mean(np.abs(raw_filled))), float(np.mean(np.abs(px_filled))))
    if series_level < zero_threshold:
        max_pct, months_differing = 0.0, 0
    else:
        excess = np.maximum(np.abs(raw_filled - px_filled) - rounding_allowance, 0.0)
        max_pct = 100.0 * float(excess.max()) / series_level
        months_differing = int((excess > series_rel_tol * series_level).sum())
    return float(f"{max_pct:.4g}"), months_differing, "AGREE" if months_differing == 0 else "DIFFER"
def build_audit_candidates(sources, raw_parts, monthly_columns):
    """Monthly series of EVERY raw resource of the table's raw measure(s), for the mapping audit. Returns candidate_names, candidate_matrix (None when there is no candidate)."""
    candidate_names, candidate_matrix = [], None
    for source in sources:
        source_part = raw_parts.get((source["fkey"], source["coll"]))
        if source_part is None or len(source_part) == 0:
            continue
        needed_source_columns = list(source["derived"]) if source["derived"] else [source["raw_col"]]
        if any(c not in source_part.columns for c in needed_source_columns):
            continue
        source_values = (source_part[needed_source_columns].sum(axis=1, min_count=1) if source["derived"] else source_part[source["raw_col"]]) * source["factor"]
        source_frame = pd.DataFrame({"id": source_part[source["id_col"]].astype(str), "m": source_part["Month Label"], "v": source_values})
        source_pivot = source_frame.groupby(["id", "m"])["v"].sum().unstack("m").reindex(columns=monthly_columns)
        candidate_names += source_pivot.index.tolist()
        candidate_matrix = source_pivot.to_numpy(dtype=float) if candidate_matrix is None else np.vstack([candidate_matrix, source_pivot.to_numpy(dtype=float)])
    return candidate_names, (np.nan_to_num(candidate_matrix) if candidate_matrix is not None else None)
def audit_section_row_mapping(table_number, table_title, raw_df, px_df, raw_positions, px_positions, px_display, raw_name_lookup, monthly_columns, table3_px_values, sources, raw_parts, rounding_step, audit_rel_tol, zero_threshold):
    """Mapping audit of one section: for EVERY PLEXOS row, is the raw row the comparison used the right one (month by month)? When not, every raw resource is tried and the best match is reported with a suggested maptable_ fix. Returns the audit rows."""
    audit_raw_all = to_numeric_matrix(raw_df[monthly_columns])
    audit_px_all = to_numeric_matrix(px_df[monthly_columns])
    audit_candidate_names, audit_candidate_matrix = build_audit_candidates(sources, raw_parts, monthly_columns)
    audit_rounding_per_month = rounding_allowance_per_month(sources, rounding_step)
    audit_rows = []
    for key in sorted(px_positions):
        for occurrence, px_position in enumerate(px_positions[key]):
            if table_number == "3" and key in table3_px_values and occurrence < len(table3_px_values[key]):
                audit_px_series = np.nan_to_num(np.asarray(table3_px_values[key][occurrence], dtype=float))
            else:
                audit_px_series = np.nan_to_num(audit_px_all[px_position])
            px_abs_sum = float(np.abs(audit_px_series).sum())
            has_code_raw = key in raw_positions and occurrence < len(raw_positions[key])
            code_names = raw_name_lookup.get(key, "") if has_code_raw else ""
            code_name_parts = [part.strip() for part in str(code_names).split(" + ") if part.strip()]
            allowance_single = audit_rounding_per_month * len(monthly_columns)
            allowance_code = allowance_single * max(1, len(code_name_parts))
            tolerance_single = audit_rel_tol * px_abs_sum + allowance_single
            tolerance_code = audit_rel_tol * px_abs_sum + allowance_code
            code_difference = np.nan
            if has_code_raw:
                audit_raw_series = np.nan_to_num(audit_raw_all[raw_positions[key][occurrence]])
                code_difference = float(np.abs(audit_raw_series - audit_px_series).sum()) / px_abs_sum if px_abs_sum > zero_threshold else (0.0 if float(np.abs(audit_raw_series).sum()) < zero_threshold else np.inf)
            code_agrees = has_code_raw and (np.isfinite(code_difference)) and (code_difference * px_abs_sum <= tolerance_code if px_abs_sum > zero_threshold else code_difference == 0.0)
            best_name, best_difference, tie_count = "", np.nan, 0
            if px_abs_sum > zero_threshold and audit_candidate_matrix is not None and len(audit_candidate_names) > 0:
                candidate_sums = np.abs(audit_candidate_matrix - audit_px_series).sum(axis=1)
                best_index = int(np.argmin(candidate_sums))
                best_difference = float(candidate_sums[best_index]) / px_abs_sum
                best_name = audit_candidate_names[best_index]
                tie_count = int((candidate_sums <= candidate_sums[best_index] + 1e-9).sum())
            best_matches = (not np.isnan(best_difference)) and best_difference * px_abs_sum <= tolerance_single
            if px_abs_sum <= zero_threshold:
                verdict = "PLEXOS row is all zero: raw side cannot be identified from values" if not has_code_raw else ("OK: PLEXOS row and raw row are both zero" if code_difference == 0.0 else "RAW HAS VALUES, PLEXOS ROW IS ALL ZERO")
                fix = ""
            elif code_agrees:
                verdict, fix = "OK: raw row matches the PLEXOS row month by month", ""
            elif has_code_raw and best_matches and best_name not in code_name_parts:
                verdict = "WRONG RAW SOURCE: the raw row used differs from the PLEXOS row, a different raw resource matches it"
                fix = f"maptable_: printed '{px_display.get(key, key)}' <- raw '{best_name}'" + (f" ({tie_count} raw resources match equally)" if tie_count > 1 else "")
            elif has_code_raw and best_matches:
                verdict, fix = "RAW ROW DIFFERS: the raw resource used matches alone but the row built from it does not (other raw names or a measure / group definition add to it)", ""
            elif has_code_raw:
                verdict, fix = "RAW ROW DIFFERS: no single raw resource matches (sum of several resources, a different measure, or data not in the raw workbook)", ""
            elif best_matches:
                verdict = "NO RAW ROW: the PLEXOS row has no raw counterpart in the comparison, but a raw resource matches it"
                fix = f"maptable_: printed '{px_display.get(key, key)}' <- raw '{best_name}'" + (f" ({tie_count} raw resources match equally)" if tie_count > 1 else "")
            else:
                verdict, fix = "NO RAW ROW: the PLEXOS row has no raw counterpart and no single raw resource matches it", ""
            audit_rows.append({"Table Number": table_number, "Table Title": table_title, "PLEXOS Row Title": px_display.get(key, key), "Occurrence": occurrence + 1, "Raw Data Name(s) Used By The Code": code_names,
                               "Code Raw Row vs PLEXOS (% of PLEXOS level)": float(f"{100 * code_difference:.4g}") if (not np.isnan(code_difference) and np.isfinite(code_difference)) else code_difference,
                               "Best Matching Raw Resource": best_name, "Best Match vs PLEXOS (% of PLEXOS level)": float(f"{100 * best_difference:.4g}") if not np.isnan(best_difference) else np.nan,
                               "Verdict": verdict, "Suggested Fix": fix})
    return audit_rows
def split_presence_sections(results_df, status_column="Section Status"):
    """Split a row-presence results table. Returns results_df (Raw Present / PLEXOS Present forced to real booleans), compared_sections (on both sides), unmapped_sections (N/A: no counterpart) and section_level_misses (FAIL sections missing from PLEXOS)."""
    results_df = results_df.copy()
    results_df["Raw Present"] = results_df["Raw Present"].astype(bool)
    results_df["PLEXOS Present"] = results_df["PLEXOS Present"].astype(bool)
    compared_sections = results_df[results_df["Raw Present"] & results_df["PLEXOS Present"]]
    unmapped_sections = results_df[results_df[status_column].astype(str).str.startswith("N/A")]
    section_level_misses = results_df[(results_df[status_column] == "FAIL") & ~results_df["PLEXOS Present"]]
    return results_df, compared_sections, unmapped_sections, section_level_misses
def detect_double_counting(ratio_series, row_count, ratio_low, ratio_high, warn_share):
    """Double-count detector: how many rows have a Raw / PLEXOS mean ratio in the band that signals raw values counted twice. Returns near_double_rows, near_double_share, double_count_suspected."""
    near_double_rows = int(((ratio_series >= ratio_low) & (ratio_series <= ratio_high)).sum())
    near_double_share = (near_double_rows / row_count) if row_count > 0 else 0.0
    return near_double_rows, near_double_share, near_double_share > warn_share
def read_plexos_section_values(plexos_rows, in_scope_tables, month_labels, skip_sections=("3",)):
    """Independent re-read of the monthly values of every in-scope Standard Report row straight from the CSV rows (no DataFrame, no table cache). Returns {(section, normalized title): [one array per occurrence]}."""
    independent_px = {}
    standard_header_re = re.compile(r"^\(\s*(\d+[a-zA-Z]?)\s*\)")
    independent_month_re = re.compile(r"^[A-Za-z]{3}-\d{4}$")
    independent_section, independent_positions = None, None
    for r in plexos_rows:
        stripped = [str(c).strip() for c in r]
        non_blank = [c for c in stripped if c]
        if not non_blank:
            continue
        header_hit = standard_header_re.match(" ".join(non_blank))
        if header_hit:
            independent_section, independent_positions = header_hit.group(1).lower(), None
            continue
        if independent_section is None or independent_section not in in_scope_tables or independent_section in skip_sections:
            continue
        if independent_positions is None:
            if any(independent_month_re.match(c) for c in stripped):
                independent_positions = {}
                for cell_index, cell_text in enumerate(stripped):
                    if cell_text != "" and cell_text not in independent_positions:
                        independent_positions[cell_text] = cell_index
            continue
        independent_label = normalize_text(stripped[0])
        if independent_label == "" or independent_label == "total" or independent_label.startswith("("):
            continue
        independent_values = np.full(len(month_labels), np.nan)
        for month_index, month_name in enumerate(month_labels):
            cell_position = independent_positions.get(month_name)
            if cell_position is not None and cell_position < len(r):
                try:
                    independent_values[month_index] = float(str(r[cell_position]).replace(",", "").replace("$", "").replace("%", "").strip())
                except ValueError:
                    pass
        independent_px.setdefault((independent_section, independent_label), []).append(independent_values)
    return independent_px
def crosscheck_plexos_statistics(magnitude_results, independent_px, magnitude_stats, rtol):
    """Compare the PLEXOS statistics of the results with the independent CSV re-read (Standard Report rows except Table 3; repeated titles are skipped). Returns rows_checked, differences DataFrame."""
    crosscheck_checked, crosscheck_bad = 0, []
    if not magnitude_results.empty:
        cross_frame = magnitude_results[(magnitude_results["Report"] == "Standard Report") & (magnitude_results["Table Number"].astype(str) != "3")]
        for cross_row in cross_frame.to_dict("records"):
            arrays_found = independent_px.get((str(cross_row["Table Number"]), normalize_text(cross_row["Row Title"])))
            if arrays_found is None or len(arrays_found) != 1:
                continue
            cross_values = arrays_found[0][~np.isnan(arrays_found[0])]
            if cross_values.size > 0:
                cross_expected = (cross_values.min(), cross_values.max(), cross_values.mean(), np.median(cross_values))
            else:
                cross_expected = (np.nan, np.nan, np.nan, np.nan)
            crosscheck_checked += 1
            for stat_name, expected_value in zip(magnitude_stats, cross_expected):
                reported_value = cross_row[f"PLEXOS {stat_name}"]
                if pd.isna(expected_value) and pd.isna(reported_value):
                    continue
                if pd.isna(expected_value) or pd.isna(reported_value) or not np.isclose(float(reported_value), float(expected_value), rtol=rtol, atol=1e-9):
                    crosscheck_bad.append({"Table Number": cross_row["Table Number"], "Row Title": cross_row["Row Title"], "Statistic": stat_name, "PLEXOS value in the results": reported_value, "Re-read from the Standard Report CSV": expected_value})
    return crosscheck_checked, pd.DataFrame(crosscheck_bad, columns=["Table Number", "Row Title", "Statistic", "PLEXOS value in the results", "Re-read from the Standard Report CSV"])
def build_stat_magnitude_summary(magnitude_results, bucket_column, match_column):
    """Per-statistic magnitude report: ONE ROW PER (Report, Table Number); each magnitude bucket (highest power of ten down to the smallest, then Zero, then No Data) becomes a Pass / Fail column pair, then Total Pass / Total Fail / Row Total."""
    if magnitude_results.empty:
        return pd.DataFrame(columns=["Report", "Table Number", "Total Pass", "Total Fail", "Row Total"])
    long_summary = magnitude_results.groupby(["Report", "Table Number", bucket_column], as_index=False).agg(Total_Rows=(match_column, "count"), Pass_Count=(match_column, "sum"))
    long_summary["Fail_Count"] = long_summary["Total_Rows"] - long_summary["Pass_Count"]
    buckets_present = sorted(set(long_summary[bucket_column]))
    ordered_buckets = sorted([b for b in buckets_present if b.startswith("10^")], key=lambda b: int(b.split("^")[1]), reverse=True)
    if "Zero" in buckets_present:
        ordered_buckets.append("Zero")
    if "No Data" in buckets_present:
        ordered_buckets.append("No Data")
    pass_wide = long_summary.pivot_table(index=["Report", "Table Number"], columns=bucket_column, values="Pass_Count", fill_value=0, aggfunc="sum")
    fail_wide = long_summary.pivot_table(index=["Report", "Table Number"], columns=bucket_column, values="Fail_Count", fill_value=0, aggfunc="sum")
    stat_summary = pd.DataFrame(index=pass_wide.index)
    for bucket in ordered_buckets:
        stat_summary[f"{bucket} Pass"] = pass_wide[bucket].astype(int) if bucket in pass_wide.columns else 0
        stat_summary[f"{bucket} Fail"] = fail_wide[bucket].astype(int) if bucket in fail_wide.columns else 0
    pass_columns = [f"{bucket} Pass" for bucket in ordered_buckets]
    fail_columns = [f"{bucket} Fail" for bucket in ordered_buckets]
    stat_summary["Total Pass"] = stat_summary[pass_columns].sum(axis=1) if pass_columns else 0
    stat_summary["Total Fail"] = stat_summary[fail_columns].sum(axis=1) if fail_columns else 0
    stat_summary["Row Total"] = stat_summary["Total Pass"] + stat_summary["Total Fail"]
    stat_summary = stat_summary.reset_index()
    stat_summary["Report Str"] = stat_summary["Report"].astype(str)
    stat_summary["Table Number Str"] = stat_summary["Table Number"].astype(str)
    stat_summary = stat_summary.sort_values(by=["Report Str", "Table Number Str"]).drop(columns=["Report Str", "Table Number Str"]).reset_index(drop=True)
    ordered_columns = ["Report", "Table Number", "Total Pass", "Total Fail"]
    for bucket in ordered_buckets:
        ordered_columns.append(f"{bucket} Pass")
        ordered_columns.append(f"{bucket} Fail")
    ordered_columns.append("Row Total")
    return stat_summary[ordered_columns]
def verify_stat_report_csv(stat_path, expected_row_total):
    """Read a per-statistic magnitude report back. Returns file_ok, columns_ok, rowtotal_ok (Row Total sums to expected_row_total), parity_ok (Total Pass + Total Fail = Row Total on every line)."""
    if not Path(stat_path).is_file():
        return False, False, False, False
    try:
        readback_stat = pd.read_csv(stat_path)
    except pd.errors.EmptyDataError:
        readback_stat = pd.DataFrame()
    columns_ok = all(c in readback_stat.columns for c in ["Report", "Table Number", "Total Pass", "Total Fail", "Row Total"])
    rowtotal_ok = int(readback_stat["Row Total"].sum()) == expected_row_total if columns_ok else False
    parity_ok = bool((readback_stat["Total Pass"] + readback_stat["Total Fail"] == readback_stat["Row Total"]).all()) if columns_ok else False
    return True, columns_ok, rowtotal_ok, parity_ok
def build_table_sources_from_coverage(cov_df, class_to_raw, derived_measures, custom_overrides):
    """table_sources ({table key: [raw measure source per Blueprint row]}) rebuilt from the coverage table that extract_blueprint_sections already returns. Use it when that function has no table_sources parameter."""
    table_sources = {}
    for cov in cov_df.to_dict("records"):
        if not str(cov["Status"]).startswith("EXTRACTED") or str(cov["Pattern"]) == "monthly-summary":
            continue
        eff_cls, eff_prop = str(cov["Class"]).lower(), cov["Property"]
        if (cov["Table"], eff_cls, eff_prop) in custom_overrides:
            eff_cls, eff_prop = custom_overrides[(cov["Table"], eff_cls, eff_prop)][:2]
        fkey, coll, id_col = class_to_raw[eff_cls]
        derived = derived_measures.get((fkey, coll, eff_prop))
        table_sources.setdefault(cov["Table"], []).append({"fkey": fkey, "coll": coll, "id_col": id_col, "raw_col": cov["Raw Column"], "derived": derived, "factor": cov["Unit Factor"], "rounding_units": len(derived) if derived else 1})
    return table_sources
################################################################################################################################################################################
#3.03D
################################################################################################################################################################################
def build_rating_section_row_jobs(report_name, section_key, table_label, table_title, category, alias, raw_df, px_df, month_labels, total_pattern, raw_name_lookup):
    """Screening jobs of ONE kind of Ratings Report row (alias 'MW' = the rows ending in ':MW', 'MBTU' = the rows ending in ':MBTU', compared ignoring case) of ONE rating period, like build_section_row_jobs does for a Standard section: ONE job per matched row occurrence (row title + occurrence, the title compared ignoring case and extra spaces), the raw side from the raw counterpart table of the Ratings Report (Generation (GWh) x 1000 for ':MW', Offtake (BBtu) x 1000 of Generator.Fuels for ':MBTU', Generator.Start Fuels excluded) and the output side from the Ratings Report. Only the monthly columns are used (Tot-YYYY / Total are excluded). table_label is the Table Number written to the results ('atc:MW'), table_title its title. Returns jobs, unmatched_rows (rows on one side only), excluded_cols (Tot-YYYY / Total columns left out), monthly_cols, log_record."""
    suffix = ":" + str(alias).strip().lower()
    keep_rows = lambda frame: frame[frame.iloc[:, 0].fillna("").astype(str).str.strip().str.lower().str.endswith(suffix)].reset_index(drop=True)
    raw_part, px_part = keep_rows(raw_df), keep_rows(px_df)
    monthly_cols = [c for c in month_labels if (c in raw_part.columns) and (c in px_part.columns)]
    excluded_cols = [str(c) for c in px_part.columns if total_pattern.match(str(c))]
    raw_block, px_block = to_numeric_matrix(raw_part[monthly_cols]), to_numeric_matrix(px_part[monthly_cols])
    raw_pos, raw_disp = index_row_positions(raw_part)
    px_pos, px_disp = index_row_positions(px_part)
    jobs = []
    for key in sorted(set(raw_pos) & set(px_pos)):
        for occurrence in range(min(len(raw_pos[key]), len(px_pos[key]))):
            jobs.append({"Job Type": "Row", "Category": category, "Report": report_name, "Table Number": table_label, "Table Title": table_title, "Row Title": px_disp.get(key, raw_disp.get(key, key)),
                         "Raw Data Name(s)": raw_name_lookup.get(key, ""), "Occurrence": occurrence + 1, "raw": raw_block[raw_pos[key][occurrence]], "px": px_block[px_pos[key][occurrence]], "extras": {}})
    unmatched_rows = [{"Report": report_name, "Table Number": table_label, "Row Title": px_disp.get(key, raw_disp.get(key, key)), "Side": "Raw data only" if key in raw_pos else "PLEXOS output only"} for key in sorted(set(raw_pos) ^ set(px_pos))]
    if jobs:
        log_record = build_section_log_record(report_name, table_label, table_title, category, "EVALUATED", len(jobs), "")
    else:
        log_record = build_section_log_record(report_name, table_label, table_title, category, "NOT EVALUATED", 0, f"no matched ':{alias}' rows were available to screen")
    return jobs, unmatched_rows, excluded_cols, monthly_cols, log_record
def build_abnormality_pivot(row_results, categories):
    """Pivot: one summary row per category followed by one row per table; the category values are the straight average of the tables' own values. REPLACES the existing function: the Report column is read from the rows of the category / table (it was always 'Standard Report'), so a category of Ratings Report rows is labeled correctly; for Standard Report rows the result is identical."""
    pivot_rows = []
    for pivot_category in categories:
        category_df = row_results[row_results["Category"] == pivot_category] if not row_results.empty else row_results
        if category_df.empty:
            continue
        table_rows = []
        for table_label in category_df["Table Number"].drop_duplicates().tolist():
            table_subset = category_df[category_df["Table Number"] == table_label]
            table_rows.append({"Report": table_subset["Report"].iloc[0], "Row Labels": table_subset["Table Title"].iloc[0], "Raw Table Average": table_subset["Raw Table Average"].iloc[0], "PLEXOS Table Average": table_subset["PLEXOS Table Average"].iloc[0],
                               "Raw Table Sum": table_subset["Raw Table Sum"].iloc[0], "PLEXOS Table Sum": table_subset["PLEXOS Table Sum"].iloc[0],
                               "Percentage of Abnormal Rows": round(table_subset["Row Outside 3 Raw Standard Deviations"].mean(), 3), "Notes": "", "Corrective Action": ""})
        pivot_rows.append({"Report": category_df["Report"].iloc[0], "Row Labels": pivot_category, "Raw Table Average": float(np.mean([r["Raw Table Average"] for r in table_rows])), "PLEXOS Table Average": float(np.mean([r["PLEXOS Table Average"] for r in table_rows])),
                           "Raw Table Sum": float(np.mean([r["Raw Table Sum"] for r in table_rows])), "PLEXOS Table Sum": float(np.mean([r["PLEXOS Table Sum"] for r in table_rows])),
                           "Percentage of Abnormal Rows": "Average of tables averages", "Notes": "", "Corrective Action": ""})
        pivot_rows.extend(table_rows)
    return pd.DataFrame(pivot_rows, columns=["Report", "Row Labels", "Raw Table Average", "PLEXOS Table Average", "Raw Table Sum", "PLEXOS Table Sum", "Percentage of Abnormal Rows", "Notes", "Corrective Action"])
def check_required_tables_evaluated(section_results, category, required_tables, heading, no_counterpart, ratings_no_raw_reason, ratings_line=None):
    """Steps 2 and 3: print the sections of one category and check that every required table was evaluated. Returns True when none is missing. REPLACES the existing function: the optional ratings_line replaces the line about the Ratings Report (the default text says the Ratings sections have no raw counterpart, which is no longer true once the Ratings raw counterpart is built)."""
    category_log = section_results[section_results["Category"] == category]
    missing_tables = [t for t in required_tables if t not in set(category_log[category_log["Status"] == "EVALUATED"]["Table Number"])]
    print(f"{heading} (required: {required_tables})")
    for _, r in category_log.iterrows():
        print(f"  [Standard Report] Table {r['Table Number']}: {r['Status']} ({r['Matched Rows']} matched row(s)){' -- ' + r['Note'] if r['Note'] else ''}")
    print(ratings_line if ratings_line is not None else f"  [Ratings Report] N/A -- {ratings_no_raw_reason}; the applicable Rating sections are listed as '{no_counterpart}' (not failures)")
    if missing_tables:
        print(f"  Missing or not evaluated: {missing_tables}")
    return len(missing_tables) == 0
def make_report_headers_unique(reports):
    """Rename duplicate column headers in every parsed table of every report (in place). Returns the number of tables changed."""
    tables_changed = 0
    for report_name, report_data in reports.items():
        for tables_key in ("PLEXOS_tables", "Raw_tables"):
            for table_number, table in (report_data.get(tables_key) or {}).items():
                frame = table["data"] if isinstance(table, dict) and "data" in table else table
                if not hasattr(frame, "columns") or not frame.columns.duplicated().any():
                    continue
                seen_headers, unique_headers = {}, []
                for header in frame.columns:
                    if header in seen_headers:
                        seen_headers[header] += 1
                        unique_headers.append(f"{header}.{seen_headers[header]}")
                    else:
                        seen_headers[header] = 0
                        unique_headers.append(header)
                frame.columns = unique_headers
                tables_changed += 1
    return tables_changed
def count_breakdown_rows(reports, breakdown_rows):
    """Count the (Primary) / (Secondary) / (Startup) / (Topping) sub-rows of every PLEXOS section, BEFORE the structural rows are removed. Returns {(report_name, table_number): count}."""
    breakdown_rows_removed = {}
    for report_name, report_config in reports.items():
        for table_number, table in report_config["PLEXOS_tables"].items():
            data = table["data"]
            if len(data.columns) == 0:
                continue
            breakdown_rows_removed[(report_name, table_number)] = int(normalize_series(data.iloc[:, 0]).isin(breakdown_rows).sum())
    return breakdown_rows_removed
def verify_all_periods_only(raw_frames, measure_columns, standard_timeslice, results_folder, file_name, required=True):
    """Timeslice rule: the raw measure columns may only use the rows whose Timeslice is the standard one ('All Periods'). For every raw sheet and measure column present: values used, rows of another Timeslice still in the frame (must be 0), the sum used against the 'All Periods' sum and the all-Timeslice sum of the UNFILTERED sheet (SIT_RAW_CACHE). Prints and saves the table. Returns check_ok, check_df."""
    raw_cache = globals().get("SIT_RAW_CACHE")
    standard_text = str(standard_timeslice).strip().lower()
    sheet_names = {"df_gen": "Generator", "df_reg": "Region", "df_bat": "Battery"}
    check_rows = []
    for frame_key, frame in raw_frames.items():
        measures = [c for c in measure_columns if c in frame.columns]
        if not measures:
            continue
        timeslice_column = find_normalized_column(frame, "timeslice")
        other_rows = None if timeslice_column is None else int((frame[timeslice_column].astype(str).str.strip().str.lower() != standard_text).sum())
        unfiltered = raw_cache.get(frame_key) if isinstance(raw_cache, dict) else None
        unfiltered_timeslice = find_normalized_column(unfiltered, "timeslice") if isinstance(unfiltered, pd.DataFrame) else None
        for measure in measures:
            used_values = pd.to_numeric(frame[measure], errors="coerce")
            used_sum = float(used_values.sum())
            all_periods_sum = all_timeslices_sum = np.nan
            if unfiltered_timeslice is not None and measure in unfiltered.columns:
                unfiltered_values = pd.to_numeric(unfiltered[measure], errors="coerce")
                is_standard = unfiltered[unfiltered_timeslice].astype(str).str.strip().str.lower() == standard_text
                all_periods_sum, all_timeslices_sum = float(unfiltered_values[is_standard].sum()), float(unfiltered_values.sum())
            if timeslice_column is None:
                status = "FAIL (no Timeslice column)" if required else "N/A (no Timeslice column)"
            elif other_rows > 0:
                status = "FAIL (rows of another Timeslice are used)"
            elif np.isnan(all_periods_sum):
                status = "PASS (rows only; the unfiltered sheet is not in the session cache)"
            elif np.isclose(used_sum, all_periods_sum, rtol=1e-9, atol=1e-9):
                status = "PASS"
            else:
                status = "FAIL (the sum used differs from the All Periods sum)"
            check_rows.append({"Raw Sheet": sheet_names.get(frame_key, frame_key), "Measure": measure, "Values Used": int(used_values.notna().sum()), "Rows Not All Periods": other_rows,
                               "Sum Used": used_sum, "All Periods Sum (unfiltered)": all_periods_sum, "All Timeslices Sum (unfiltered)": all_timeslices_sum, "Status": status})
    check_df = pd.DataFrame(check_rows, columns=["Raw Sheet", "Measure", "Values Used", "Rows Not All Periods", "Sum Used", "All Periods Sum (unfiltered)", "All Timeslices Sum (unfiltered)", "Status"])
    save_results_csv(check_df, results_folder, file_name)
    check_ok = bool((not check_df.empty) and check_df["Status"].str.startswith(("PASS", "N/A")).all())
    print(f"  Timeslice rule ('{standard_timeslice}' only) for the raw measures ({len(check_df)} sheet / measure combination(s); written to {file_name}):")
    print(check_df.to_string(index=False, float_format=lambda value: f"{value:,.2f}"))
    return check_ok, check_df
def build_section_log_record(report_name, table_number, table_title, category, status, matched_rows, note):
    """One section-log record (a section considered by the screening)."""
    return {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Category": category, "Status": status, "Matched Rows": matched_rows, "Note": note}
def describe_missing_section(table_number, table_title, category, raw_entry, px_entry, no_counterpart):
    """Section-log record of an in-scope section that is not on both sides: an 'Other' section without a raw counterpart is N/A (not a failure), any other missing 'Other' section is NOT EVALUATED, a missing generation / cost table is a FAIL."""
    where_missing = "raw data and PLEXOS output" if (raw_entry is None and px_entry is None) else ("raw data" if raw_entry is None else "PLEXOS output")
    if category == "Other":
        if raw_entry is None and px_entry is not None:
            return build_section_log_record("Standard Report", table_number, table_title, category, "N/A - " + no_counterpart, 0, "no solution.zip counterpart for this section (not a failure)")
        return build_section_log_record("Standard Report", table_number, table_title, category, "NOT EVALUATED", 0, f"the section is missing from the {where_missing}")
    return build_section_log_record("Standard Report", table_number, table_title, category, "FAIL", 0, f"required {category.lower()} table is missing from the {where_missing}")
def build_section_row_jobs(table_number, table_title, category, raw_df, px_df, month_labels, total_pattern, table3_px_values, raw_name_lookup):
    """Screening jobs of one section present on both sides: ONE job per matched row occurrence (row title + occurrence; Table 3 PLEXOS = Primary + Secondary + Topping). Returns jobs, section_block (numeric monthly blocks and row positions, reused by cost-per-MWh), unmatched_rows (rows on one side only), excluded_cols (Tot-YYYY / Total columns left out), table3_rows_rebuilt, log_record."""
    monthly_cols = [c for c in month_labels if (c in raw_df.columns) and (c in px_df.columns)]
    excluded_cols = [str(c) for c in px_df.columns if total_pattern.match(str(c))]
    raw_block = to_numeric_matrix(raw_df[monthly_cols])
    px_block = to_numeric_matrix(px_df[monthly_cols])
    raw_pos, raw_disp = index_row_positions(raw_df)
    px_pos, px_disp = index_row_positions(px_df)
    table3_month_index = [month_labels.index(c) for c in monthly_cols]
    jobs, table3_rows_rebuilt = [], 0
    for key in sorted(set(raw_pos) & set(px_pos)):
        for occurrence in range(min(len(raw_pos[key]), len(px_pos[key]))):
            job_px_series = px_block[px_pos[key][occurrence]]
            if table_number == "3" and key in table3_px_values and occurrence < len(table3_px_values[key]):
                job_px_series = np.asarray(table3_px_values[key][occurrence], dtype=float)[table3_month_index]
                table3_rows_rebuilt += 1
            jobs.append({"Job Type": "Row", "Category": category, "Report": "Standard Report", "Table Number": table_number, "Table Title": table_title, "Row Title": px_disp.get(key, raw_disp.get(key, key)),
                         "Raw Data Name(s)": raw_name_lookup.get(key, ""), "Occurrence": occurrence + 1, "raw": raw_block[raw_pos[key][occurrence]], "px": job_px_series, "extras": {}})
    unmatched_rows = [{"Report": "Standard Report", "Table Number": table_number, "Row Title": px_disp.get(key, raw_disp.get(key, key)), "Side": "Raw data only" if key in raw_pos else "PLEXOS output only"} for key in sorted(set(raw_pos) ^ set(px_pos))]
    section_block = {"raw_block": raw_block, "px_block": px_block, "raw_pos": raw_pos, "px_pos": px_pos, "raw_disp": raw_disp, "px_disp": px_disp, "monthly_cols": monthly_cols, "title": table_title}
    if jobs:
        log_record = build_section_log_record("Standard Report", table_number, table_title, category, "EVALUATED", len(jobs), "")
    else:
        log_record = build_section_log_record("Standard Report", table_number, table_title, category, "FAIL" if category != "Other" else "NOT EVALUATED", 0, "no matched rows were available to screen")
    return jobs, section_block, unmatched_rows, excluded_cols, table3_rows_rebuilt, log_record
def build_cost_per_mwh_jobs(section_blocks, generation_table, cost_table, raw_name_lookup, breakdown_rows):
    """Cost-per-MWh jobs: raw Fuel Cost ($000) / Generation (GWh) and output Table 6 Fuel Cost / Table 2 Generation per resource-month. A month with zero generation gives no value (never infinity); (Primary) / (Secondary) / (Startup) / (Topping) rows are skipped. Returns cpm_jobs, cpm_month_stats, breakdown_titles_seen, cpm_months, log_record."""
    cpm_month_stats = {"raw_excluded_months": 0, "px_excluded_months": 0, "values_checked": 0, "non_finite_values": 0}
    if not ((generation_table in section_blocks) and (cost_table in section_blocks)):
        return [], cpm_month_stats, [], [], build_section_log_record("Standard Report", f"{cost_table}/{generation_table}", "Cost per MWh", "Cost per MWh", "FAIL", 0, f"Table {generation_table} and/or Table {cost_table} is missing on one side, so cost-per-MWh cannot be calculated")
    gen_block_info, cost_block_info = section_blocks[generation_table], section_blocks[cost_table]
    cpm_months = [c for c in gen_block_info["monthly_cols"] if c in cost_block_info["monthly_cols"]]
    month_index_gen = [gen_block_info["monthly_cols"].index(c) for c in cpm_months]
    month_index_cost = [cost_block_info["monthly_cols"].index(c) for c in cpm_months]
    common_keys = sorted(set(gen_block_info["raw_pos"]) & set(gen_block_info["px_pos"]) & set(cost_block_info["raw_pos"]) & set(cost_block_info["px_pos"]))
    cpm_title = f"Cost per MWh (Table {cost_table} Fuel Cost / Table {generation_table} Generation)"
    cpm_jobs, breakdown_titles_seen = [], []
    for key in common_keys:
        display_title = cost_block_info["px_disp"].get(key, key)
        if key.startswith("(") or key in breakdown_rows:
            breakdown_titles_seen.append(display_title)
            continue
        occurrences = min(len(gen_block_info["raw_pos"][key]), len(gen_block_info["px_pos"][key]), len(cost_block_info["raw_pos"][key]), len(cost_block_info["px_pos"][key]))
        for occurrence in range(occurrences):
            raw_gen_mwh = gen_block_info["raw_block"][gen_block_info["raw_pos"][key][occurrence]][month_index_gen]
            raw_cost_dollars = cost_block_info["raw_block"][cost_block_info["raw_pos"][key][occurrence]][month_index_cost]
            px_gen_mwh = gen_block_info["px_block"][gen_block_info["px_pos"][key][occurrence]][month_index_gen]
            px_cost_dollars = cost_block_info["px_block"][cost_block_info["px_pos"][key][occurrence]][month_index_cost]
            raw_gen_gwh = raw_gen_mwh / 1000.0
            raw_cost_thousands = raw_cost_dollars / 1000.0
            with np.errstate(divide="ignore", invalid="ignore"):
                raw_cpm = np.where(np.isfinite(raw_gen_gwh) & (raw_gen_gwh != 0), raw_cost_thousands / raw_gen_gwh, np.nan)
                px_cpm = np.where(np.isfinite(px_gen_mwh) & (px_gen_mwh != 0), px_cost_dollars / px_gen_mwh, np.nan)
            raw_excluded = int((np.isfinite(raw_gen_gwh) & (raw_gen_gwh == 0)).sum())
            px_excluded = int((np.isfinite(px_gen_mwh) & (px_gen_mwh == 0)).sum())
            cpm_month_stats["raw_excluded_months"] += raw_excluded
            cpm_month_stats["px_excluded_months"] += px_excluded
            cpm_month_stats["values_checked"] += int(np.isfinite(raw_cpm).sum() + np.isfinite(px_cpm).sum())
            cpm_month_stats["non_finite_values"] += int(np.isinf(raw_cpm).sum() + np.isinf(px_cpm).sum())
            cpm_jobs.append({"Job Type": "CostPerMWh", "Category": "Cost per MWh", "Report": "Standard Report", "Table Number": f"{cost_table}/{generation_table}", "Table Title": cpm_title, "Row Title": display_title,
                             "Raw Data Name(s)": raw_name_lookup.get(key, ""), "Occurrence": occurrence + 1, "raw": raw_cpm, "px": px_cpm,
                             "extras": {"Raw Fuel Cost Mean ($000)": float(np.nanmean(raw_cost_thousands)) if np.isfinite(raw_cost_thousands).any() else np.nan,
                                        "Raw Generation Mean (GWh)": float(np.nanmean(raw_gen_gwh)) if np.isfinite(raw_gen_gwh).any() else np.nan,
                                        "PLEXOS Fuel Cost Mean ($)": float(np.nanmean(px_cost_dollars)) if np.isfinite(px_cost_dollars).any() else np.nan,
                                        "PLEXOS Generation Mean (MWh)": float(np.nanmean(px_gen_mwh)) if np.isfinite(px_gen_mwh).any() else np.nan,
                                        "Raw Months Excluded (zero generation)": raw_excluded, "PLEXOS Months Excluded (zero generation)": px_excluded}})
    log_record = build_section_log_record("Standard Report", f"Table {cost_table} /Table {generation_table}", cpm_title, "Cost per MWh", "EVALUATED" if len(cpm_jobs) > 0 else "FAIL", len(cpm_jobs), "")
    return cpm_jobs, cpm_month_stats, breakdown_titles_seen, cpm_months, log_record
def screen_job(job, sd_flag_threshold, zero_threshold):
    """Screen one job: raw row mean / standard deviation (ddof=1), distance = ABS(output mean - raw mean) / raw standard deviation, flagged when the distance is greater than the threshold. A raw standard deviation of 0 is not divided (flagged only when the output mean differs). Returns the result row (dict), raw_values, px_values."""
    raw_values = job["raw"][np.isfinite(job["raw"])]
    px_values = job["px"][np.isfinite(job["px"])]
    raw_n, px_n = int(len(raw_values)), int(len(px_values))
    raw_mean = float(raw_values.mean()) if raw_n > 0 else np.nan
    px_mean = float(px_values.mean()) if px_n > 0 else np.nan
    raw_sd = float(raw_values.std(ddof=1)) if raw_n > 1 else (0.0 if raw_n == 1 else np.nan)
    unable = 1 if (raw_n == 0 or px_n == 0) else 0
    zero_variance = 1 if (unable == 0 and raw_sd <= 1e-12 * max(1.0, abs(raw_mean))) else 0
    if unable:
        distance, flag, reason = np.nan, 0, "Unable to evaluate (no numeric data on one side)"
    elif zero_variance:
        differs = not math.isclose(px_mean, raw_mean, rel_tol=1e-6, abs_tol=1e-9)
        distance, flag = np.nan, int(differs)
        reason = "Raw standard deviation is 0: not divided; flagged because the output mean differs from the raw mean" if differs else "Raw standard deviation is 0: not divided; output mean equals the raw mean"
    else:
        distance = abs(px_mean - raw_mean) / raw_sd
        flag = int(distance > sd_flag_threshold)
        reason = f"Output mean is {distance:.2f} raw standard deviations from the raw mean" + (" (> 3: abnormal)" if flag else "")
    result = {"Job Type": job["Job Type"], "Category": job["Category"], "Report": job["Report"], "Table Number": job["Table Number"], "Table Title": job["Table Title"], "Row Title": job["Row Title"],
              "Raw Data Name(s)": job["Raw Data Name(s)"], "Occurrence": job["Occurrence"], "Raw Numeric Count": raw_n, "PLEXOS Numeric Count": px_n, "Raw Row Average": raw_mean, "PLEXOS Row Average": px_mean,
              "Raw Row Standard Deviation": raw_sd, "Row Standard Deviations From Raw Average": distance, "Zero Variance Row": zero_variance, "Row Outside 3 Raw Standard Deviations": flag,
              "Row Unable to Evaluate": unable, "Screening Note": reason,
              "Raw / PLEXOS Mean Ratio": (raw_mean / px_mean) if (pd.notna(raw_mean) and pd.notna(px_mean) and abs(px_mean) >= zero_threshold) else np.nan}
    result.update(job["extras"])
    return result, raw_values, px_values
def screen_jobs(jobs, sd_flag_threshold, zero_threshold):
    """Screen every job. Returns result_rows, zero_variance_rows and table_accumulators ((job type, table number) -> the matched raw / output values of the table, for the table-wide statistics)."""
    result_rows, zero_variance_rows, table_accumulators = [], [], {}
    for job in jobs:
        result, raw_values, px_values = screen_job(job, sd_flag_threshold, zero_threshold)
        accumulator = table_accumulators.setdefault((job["Job Type"], job["Table Number"]), {"raw": [], "px": []})
        accumulator["raw"].append(raw_values)
        accumulator["px"].append(px_values)
        result_rows.append(result)
        if result["Zero Variance Row"]:
            zero_variance_rows.append(result)
    return result_rows, zero_variance_rows, table_accumulators
def round_numeric_columns(frame, decimals=5):
    """Round every numeric column of a results table (an empty table is returned unchanged)."""
    if frame.empty:
        return frame
    numeric_columns = frame.select_dtypes(include="number").columns
    frame[numeric_columns] = frame[numeric_columns].round(decimals)
    return frame
def build_results_frame(result_rows, table_accumulators, sd_flag_threshold):
    """Results table of every screened row plus the table-wide context of its table (pooled matched monthly values: sum, average, raw standard deviation, whether the output table average is more than the threshold raw standard deviations away). Rounded to 5 decimals."""
    all_results = pd.DataFrame(result_rows)
    table_stat_lookup = {}
    for table_key, accumulator in table_accumulators.items():
        raw_all = np.concatenate(accumulator["raw"]) if len(accumulator["raw"]) > 0 else np.array([])
        px_all = np.concatenate(accumulator["px"]) if len(accumulator["px"]) > 0 else np.array([])
        raw_table_mean = float(raw_all.mean()) if len(raw_all) > 0 else np.nan
        px_table_mean = float(px_all.mean()) if len(px_all) > 0 else np.nan
        raw_table_sd = float(raw_all.std(ddof=1)) if len(raw_all) > 1 else np.nan
        table_outside = int(pd.notna(raw_table_sd) and pd.notna(px_table_mean) and pd.notna(raw_table_mean) and abs(px_table_mean - raw_table_mean) > sd_flag_threshold * raw_table_sd)
        table_stat_lookup[table_key] = (float(raw_all.sum()) if len(raw_all) > 0 else np.nan, float(px_all.sum()) if len(px_all) > 0 else np.nan, raw_table_mean, px_table_mean, raw_table_sd, table_outside)
    if not all_results.empty:
        stat_frame = pd.DataFrame([table_stat_lookup.get((jt, tn), (np.nan,) * 6) for jt, tn in zip(all_results["Job Type"], all_results["Table Number"])],
                                  columns=["Raw Table Sum", "PLEXOS Table Sum", "Raw Table Average", "PLEXOS Table Average", "Raw Table Standard Deviation", "Table Average Outside 3 Raw Standard Deviations"])
        for stat_column in stat_frame.columns:
            all_results[stat_column] = stat_frame[stat_column].to_numpy()
    return round_numeric_columns(all_results)
def split_results_by_job_type(all_results, screen_columns):
    """Split the results into the row-screening results and the cost-per-MWh results (two empty tables with the screen columns when there are no results)."""
    if all_results.empty:
        return pd.DataFrame(columns=screen_columns + ["Job Type"]), pd.DataFrame(columns=screen_columns + ["Job Type"])
    return all_results[all_results["Job Type"] == "Row"].copy(), all_results[all_results["Job Type"] == "CostPerMWh"].copy()
def find_monthly_column_problems(monthly_columns_used, excluded_columns_log, month_labels, period_pattern, total_pattern):
    """Steps 4 and 5: columns that are not Mon-YYYY, sections that do not use the full monthly set, and Tot-YYYY / Total columns that leaked into the calculations. Returns step4_problems, step5_problems, total_excluded_count."""
    step4_problems, step5_problems = [], []
    for report_label, table_label, used_columns in monthly_columns_used:
        non_monthly = [c for c in used_columns if not period_pattern.match(str(c))]
        if len(non_monthly) > 0:
            step4_problems.append(f"Table {table_label}: non-monthly column(s) used {non_monthly}")
        if len(used_columns) != len(month_labels):
            step4_problems.append(f"Table {table_label}: {len(used_columns)} monthly columns used, expected {len(month_labels)}")
        leaked = [c for c in used_columns if total_pattern.match(str(c))]
        if len(leaked) > 0:
            step5_problems.append(f"Table {table_label}: total column(s) used in calculations {leaked}")
    return step4_problems, step5_problems, sum(len(excluded_columns) for _, _, excluded_columns in excluded_columns_log)
def check_required_tables_evaluated(section_results, category, required_tables, heading, no_counterpart, ratings_no_raw_reason):
    """Steps 2 and 3: print the sections of one category and check that every required table was evaluated. Returns True when none is missing."""
    category_log = section_results[section_results["Category"] == category]
    missing_tables = [t for t in required_tables if t not in set(category_log[category_log["Status"] == "EVALUATED"]["Table Number"])]
    print(f"{heading} (required: {required_tables})")
    for _, r in category_log.iterrows():
        print(f"  [Standard Report] Table {r['Table Number']}: {r['Status']} ({r['Matched Rows']} matched row(s)){' -- ' + r['Note'] if r['Note'] else ''}")
    print(f"  [Ratings Report] N/A -- {ratings_no_raw_reason}; the applicable Rating sections are listed as '{no_counterpart}' (not failures)")
    if missing_tables:
        print(f"  Missing or not evaluated: {missing_tables}")
    return len(missing_tables) == 0
def check_distance_calculation(all_results, zero_variance_results):
    """Step 7: split the rows into evaluable / divisible / zero-variance and check that every divisible row has a distance equal to ABS(PLEXOS average - raw average) / raw standard deviation, that zero-variance rows have none and are reported separately. Returns a dictionary of the pieces and step7_pass."""
    evaluable = all_results[all_results["Row Unable to Evaluate"] == 0] if not all_results.empty else all_results
    divisible = evaluable[evaluable["Zero Variance Row"] == 0] if not evaluable.empty else evaluable
    zero_var_eval = evaluable[evaluable["Zero Variance Row"] == 1] if not evaluable.empty else evaluable
    missing_distance = divisible[divisible["Row Standard Deviations From Raw Average"].isna()] if not divisible.empty else divisible
    zero_var_has_distance = zero_var_eval[zero_var_eval["Row Standard Deviations From Raw Average"].notna()] if not zero_var_eval.empty else zero_var_eval
    recomputed = (divisible["PLEXOS Row Average"] - divisible["Raw Row Average"]).abs() / divisible["Raw Row Standard Deviation"] if not divisible.empty else pd.Series([], dtype=float)
    distance_matches = bool(divisible.empty or np.allclose(recomputed.to_numpy(dtype=float), divisible["Row Standard Deviations From Raw Average"].to_numpy(dtype=float), rtol=1e-3, atol=1e-3))
    zero_var_reported = len(zero_variance_results) == len(zero_var_eval)
    step7_pass = (not evaluable.empty) and missing_distance.empty and zero_var_has_distance.empty and distance_matches and zero_var_reported
    return {"evaluable": evaluable, "divisible": divisible, "zero_var_eval": zero_var_eval, "missing_distance": missing_distance, "zero_var_has_distance": zero_var_has_distance,
            "distance_matches": distance_matches, "zero_var_reported": zero_var_reported}, bool(step7_pass)
def check_flag_consistency(divisible, all_results, sd_flag_threshold):
    """Step 8: every row with a distance greater than the threshold is flagged and no other row is; a row that could not be evaluated is never flagged. Returns step8_pass, abnormal_rows, flags_exact (the 'every row ... flagged and no other row is' check that is printed)."""
    should_flag = int((divisible["Row Standard Deviations From Raw Average"] > sd_flag_threshold).sum()) if not divisible.empty else 0
    flagged_divisible = int(divisible["Row Outside 3 Raw Standard Deviations"].sum()) if not divisible.empty else 0
    flag_consistent = bool(divisible.empty or ((divisible["Row Standard Deviations From Raw Average"] > sd_flag_threshold).astype(int) == divisible["Row Outside 3 Raw Standard Deviations"]).all())
    unable_flagged = int(all_results[(all_results["Row Unable to Evaluate"] == 1) & (all_results["Row Outside 3 Raw Standard Deviations"] == 1)].shape[0]) if not all_results.empty else 0
    abnormal_rows = all_results[all_results["Row Outside 3 Raw Standard Deviations"] == 1] if not all_results.empty else all_results
    flags_exact = flag_consistent and should_flag == flagged_divisible
    return bool((not all_results.empty) and flags_exact and unable_flagged == 0), abnormal_rows, flags_exact
def has_infinite_values(frame, columns):
    """True when any of the columns holds an infinite value (an empty table has none)."""
    return bool((not frame.empty) and any(np.isinf(frame[c].to_numpy(dtype=float)).any() for c in columns))
def select_export_columns(frame, columns):
    """The listed columns that exist in the table (an empty table is returned unchanged)."""
    return frame[[c for c in columns if c in frame.columns]] if not frame.empty else frame
def select_flagged_export_columns(frame, columns):
    """Only the abnormal rows (Row Outside 3 Raw Standard Deviations = 1), limited to the columns that exist in the table; an empty table is returned unchanged."""
    return frame[frame["Row Outside 3 Raw Standard Deviations"] == 1][[c for c in columns if c in frame.columns]] if not frame.empty else frame
def keep_flagged_rows(frame):
    """Only the rows labeled abnormal (Row Outside 3 Raw Standard Deviations = 1); an empty table is returned unchanged."""
    return frame[frame["Row Outside 3 Raw Standard Deviations"] == 1] if not frame.empty else frame
def build_abnormality_pivot(row_results, categories):
    """Pivot: one summary row per category followed by one row per table; the category values are the straight average of the tables' own values."""
    pivot_rows = []
    for pivot_category in categories:
        category_df = row_results[row_results["Category"] == pivot_category] if not row_results.empty else row_results
        if category_df.empty:
            continue
        table_rows = []
        for table_label in category_df["Table Number"].drop_duplicates().tolist():
            table_subset = category_df[category_df["Table Number"] == table_label]
            table_rows.append({"Report": "Standard Report", "Row Labels": table_subset["Table Title"].iloc[0], "Raw Table Average": table_subset["Raw Table Average"].iloc[0], "PLEXOS Table Average": table_subset["PLEXOS Table Average"].iloc[0],
                               "Raw Table Sum": table_subset["Raw Table Sum"].iloc[0], "PLEXOS Table Sum": table_subset["PLEXOS Table Sum"].iloc[0],
                               "Percentage of Abnormal Rows": round(table_subset["Row Outside 3 Raw Standard Deviations"].mean(), 3), "Notes": "", "Corrective Action": ""})
        pivot_rows.append({"Report": "Standard Report", "Row Labels": pivot_category, "Raw Table Average": float(np.mean([r["Raw Table Average"] for r in table_rows])), "PLEXOS Table Average": float(np.mean([r["PLEXOS Table Average"] for r in table_rows])),
                           "Raw Table Sum": float(np.mean([r["Raw Table Sum"] for r in table_rows])), "PLEXOS Table Sum": float(np.mean([r["PLEXOS Table Sum"] for r in table_rows])),
                           "Percentage of Abnormal Rows": "Average of tables averages", "Notes": "", "Corrective Action": ""})
        pivot_rows.extend(table_rows)
    return pd.DataFrame(pivot_rows, columns=["Report", "Row Labels", "Raw Table Average", "PLEXOS Table Average", "Raw Table Sum", "PLEXOS Table Sum", "Percentage of Abnormal Rows", "Notes", "Corrective Action"])
def build_screening_exports(results_folder, all_results, row_results, cpm_results, zero_variance_results, section_results, screen_columns, pivot_categories):
    """The exports of Step 12: label -> (path, table, abnormal_only). Every screened row (comparison files) and only the abnormal rows, for all sections, generation, costs and cost per MWh, plus the zero-variance rows, the section status and the pivot."""
    results_folder = Path(results_folder)
    generation_results = row_results[row_results["Category"] == "Generation"] if not row_results.empty else row_results
    cost_results = row_results[row_results["Category"] == "Cost"] if not row_results.empty else row_results
    cpm_columns = [c for c in screen_columns if c in cpm_results.columns] + [c for c in cpm_results.columns if c not in screen_columns and c != "Job Type"]
    zero_variance_export = select_export_columns(zero_variance_results, screen_columns + ["Job Type"]) if not zero_variance_results.empty else pd.DataFrame(columns=screen_columns)
    exports = {}
    exports["All results (comparison)"] = (results_folder / "PlexOS_3_03D_Abnormalities_ALL_Comparison.csv", select_export_columns(all_results, screen_columns), False)
    exports["All results (abnormal rows)"] = (results_folder / "PlexOS_3_03D_Abnormalities_ALL.csv", select_export_columns(keep_flagged_rows(all_results), screen_columns), True)
    exports["Generation (comparison)"] = (results_folder / "PlexOS_3_03D_Abnormalities_Generation_Comparison.csv", select_export_columns(generation_results, screen_columns), False)
    exports["Generation (abnormal rows)"] = (results_folder / "PlexOS_3_03D_Abnormalities_Generation.csv", select_flagged_export_columns(generation_results, screen_columns), True)
    exports["Costs (comparison)"] = (results_folder / "PlexOS_3_03D_Abnormalities_Costs_Comparison.csv", select_export_columns(cost_results, screen_columns), False)
    exports["Costs (abnormal rows)"] = (results_folder / "PlexOS_3_03D_Abnormalities_Costs.csv", select_flagged_export_columns(cost_results, screen_columns), True)
    exports["Cost per MWh (comparison)"] = (results_folder / "PlexOS_3_03D_Abnormalities_CostperMWH_Comparison.csv", select_export_columns(cpm_results, cpm_columns), False)
    exports["Cost per MWh (abnormal rows)"] = (results_folder / "PlexOS_3_03D_Abnormalities_CostperMWH.csv", select_flagged_export_columns(cpm_results, cpm_columns), True)
    exports["Zero-variance rows (reported separately)"] = (results_folder / "PlexOS_3_03D_ZeroVariance_Rows.csv", zero_variance_export, False)
    exports["Section status (incl. Ratings N/A)"] = (results_folder / "PlexOS_3_03D_Section_Status.csv", section_results, False)
    exports["Pivot by category and table"] = (results_folder / "PlexOS_3_03D_Abnormalities_Pivot.csv", build_abnormality_pivot(row_results, pivot_categories), False)
    return exports
def write_and_verify_exports(exports, status_text):
    """Write every export, read it back and check the row count, that the report type / section is on every row and (abnormal files) that only abnormal rows are in it. Prints one line per file. Returns {label: bool}."""
    export_checks = {}
    for export_label, (export_path, export_frame, abnormal_only) in exports.items():
        export_frame.to_csv(export_path, index=False)
        file_ok = export_path.is_file()
        rows_ok = False
        identified_ok = False
        if file_ok:
            try:
                readback = pd.read_csv(export_path, dtype={"Table Number": str})
            except pd.errors.EmptyDataError:
                readback = pd.DataFrame()
            rows_ok = len(readback) == len(export_frame)
            if "Report" in readback.columns and ("Table Number" in readback.columns or export_label.startswith("Pivot")):
                identified_ok = bool(readback.empty or readback["Report"].notna().all())
            else:
                identified_ok = bool(readback.empty and len(export_frame) == 0)
            if abnormal_only and len(readback) > 0 and "Row Outside 3 Raw Standard Deviations" in readback.columns:
                identified_ok = identified_ok and bool((readback["Row Outside 3 Raw Standard Deviations"] == 1).all())
        export_checks[export_label] = file_ok and rows_ok and identified_ok
        print(f"  {export_label}: {export_path.name} ({len(export_frame)} row(s)) -- written, row count and report/section identification verified: {status_text[export_checks[export_label]]}")
    return export_checks
def verify_screening_all_files(comparison_path, abnormal_path, all_results, screened_sections, status_text):
    """The two ALL files cover every in-scope section: the comparison file holds every screened row (abnormal or not), the abnormal file holds exactly the rows flagged in it. Prints the two checks. Returns {label: bool}."""
    readbacks = []
    for path in (comparison_path, abnormal_path):
        try:
            readbacks.append(pd.read_csv(path, dtype={"Table Number": str}))
        except pd.errors.EmptyDataError:
            readbacks.append(pd.DataFrame(columns=["Table Number", "Row Outside 3 Raw Standard Deviations"]))
    comparison_back, abnormal_back = readbacks
    comparison_tables = set(comparison_back["Table Number"].astype(str)) if "Table Number" in comparison_back.columns else set()
    sections_missing_from_comparison = [t for t in screened_sections if t not in comparison_tables]
    flagged_in_comparison = int((comparison_back["Row Outside 3 Raw Standard Deviations"] == 1).sum()) if "Row Outside 3 Raw Standard Deviations" in comparison_back.columns else 0
    abnormal_tables = set(abnormal_back["Table Number"].astype(str)) if "Table Number" in abnormal_back.columns else set()
    checks = {f"_ALL_Comparison holds every screened in-scope section ({len(screened_sections) - len(sections_missing_from_comparison)} of {len(screened_sections)}), abnormal or not": len(sections_missing_from_comparison) == 0 and len(comparison_back) == len(all_results),
              f"_ALL holds only the abnormal rows, all of them ({len(abnormal_back)} row(s) = {flagged_in_comparison} flagged in the comparison file)": len(abnormal_back) == flagged_in_comparison and abnormal_tables <= comparison_tables}
    print_status_checks(checks, status_text)
    if len(sections_missing_from_comparison) > 0:
        print(f"  PROBLEM: section(s) missing from the comparison file: {sections_missing_from_comparison}")
    return checks
def check_required_tables_evaluated_with_ratings(section_results, category, required_tables, heading, no_counterpart, ratings_no_raw_reason, ratings_line=None):
    category_log = section_results[section_results["Category"] == category]
    missing_tables = [t for t in required_tables if t not in set(category_log[category_log["Status"] == "EVALUATED"]["Table Number"])]
    print(f"{heading} (required: {required_tables})")
    for _, r in category_log.iterrows():
        print(f"  [Standard Report] Table {r['Table Number']}: {r['Status']} ({r['Matched Rows']} matched row(s)){' -- ' + r['Note'] if r['Note'] else ''}")
    print(ratings_line if ratings_line is not None else f"  [Ratings Report] N/A -- {ratings_no_raw_reason}; the applicable Rating sections are listed as '{no_counterpart}' (not failures)")
    if missing_tables:
        print(f"  Missing or not evaluated: {missing_tables}")
    return len(missing_tables) == 0
################################################################################################################################################################################
#3.03E
################################################################################################################################################################################
def restrict_to_rows_on_both_sides(raw_df, px_df):
    """Keep only the rows that exist on BOTH sides, paired on the row title WITHOUT its trailing bracketed unit ('EP Cont Gas (mmBtu )' and 'EP Cont Gas ($)' are the same contract), case and extra spaces ignored.
    Returns raw_df, px_df, note, left_out (list of (side, title))."""
    stem = lambda text: normalize_text(re.sub(r"\([^)]*\)\s*$", "", str(text)))
    raw_titles = raw_df.iloc[:, 0].fillna("").astype(str).str.strip()
    px_titles = px_df.iloc[:, 0].fillna("").astype(str).str.strip()
    raw_stems, px_stems = raw_titles.map(stem), px_titles.map(stem)
    common = set(s for s in raw_stems if s != "") & set(s for s in px_stems if s != "")
    raw_keep, px_keep = raw_stems.isin(common), px_stems.isin(common)
    left_out = [("Raw data only", t) for t in raw_titles[~raw_keep & (raw_titles != "")]] + [("PLEXOS only", t) for t in px_titles[~px_keep & (px_titles != "")]]
    note = (f"pooled on the {int(px_keep.sum())} row(s) present on both sides; left out: {int((~raw_keep & (raw_titles != '')).sum())} raw-only and {int((~px_keep & (px_titles != '')).sum())} PLEXOS-only row(s) (no raw counterpart)") if left_out else ""
    return raw_df[raw_keep].reset_index(drop=True), px_df[px_keep].reset_index(drop=True), note, left_out
def rating_expand_sections_03e(raw_tables, px_tables, section_keys):
    expanded_sections = []
    for section_key in section_keys:
        raw_section, px_section = raw_tables.get(section_key), px_tables.get(section_key)
        if raw_section is None or px_section is None:
            expanded_sections.append((section_key, raw_section, px_section, section_key))
            continue
        seen_aliases = set()
        for rating_definition in rating_definitions:
            alias_text, measure_text = rating_definition["alias"], rating_definition["measure"]
            if alias_text.lower() in seen_aliases:
                continue                                        #an alias with two definitions (Var O&M: Generator + Battery) is ONE section: its rows are selected by the alias
            seen_aliases.add(alias_text.lower())
            basis_label_text, basis_column_text = rating_alias_basis(rating_definitions, alias_text, RATING_UNIT_FACTOR)
            alias_suffix = ":" + alias_text.lower()
            alias_rows = lambda frame, suffix=alias_suffix: frame[frame.iloc[:, 0].fillna("").astype(str).str.strip().str.lower().str.endswith(suffix)].reset_index(drop=True)
            raw_alias_part, px_alias_part = alias_rows(raw_section["data"]), alias_rows(px_section["data"])
            if len(raw_alias_part) == 0 and len(px_alias_part) == 0:
                continue
            alias_title = f"{px_section['title']} :{alias_text} rows (raw {basis_label_text})"
            expanded_sections.append((f"{section_key} ({alias_text})", {"title": alias_title, "data": raw_alias_part}, {"title": alias_title, "data": px_alias_part}, section_key))
    return expanded_sections
def rating_expand_sections(raw_tables, px_tables, section_keys):
    expanded_sections = []
    for section_key in section_keys:
        raw_section, px_section = raw_tables.get(section_key), px_tables.get(section_key)
        if raw_section is None or px_section is None:
            expanded_sections.append((section_key, raw_section, px_section, section_key))
            continue
        seen_aliases = set()
        for rating_definition in rating_definitions:
            alias_text, measure_text = rating_definition["alias"], rating_definition["measure"]
            if alias_text.lower() in seen_aliases:
                continue                                        #an alias with two definitions (Var O&M: Generator + Battery) is ONE section: its rows are selected by the alias
            seen_aliases.add(alias_text.lower())
            basis_label_text, basis_column_text = rating_alias_basis(rating_definitions, alias_text, RATING_UNIT_FACTOR)
            alias_suffix = ":" + alias_text.lower()
            alias_rows = lambda frame: frame[frame.iloc[:, 0].fillna("").astype(str).str.strip().str.lower().str.endswith(alias_suffix)].reset_index(drop=True)
            raw_alias_part, px_alias_part = alias_rows(raw_section["data"]), alias_rows(px_section["data"])
            if len(raw_alias_part) == 0 and len(px_alias_part) == 0:
                continue
            alias_title = f"{px_section['title']} :{alias_text} rows (raw {basis_label_text})"
            expanded_sections.append((f"{section_key} ({alias_text})", {"title": alias_title, "data": raw_alias_part}, {"title": alias_title, "data": px_alias_part}, section_key))
    return expanded_sections
def rating_reference_with_alias_labels(reference_frame):
    relabeled_frame = reference_frame.copy()
    relabeled_frame["Table Number"] = relabeled_frame["Table Number"].astype(str)
    rating_mask = (relabeled_frame["Report"] == "Ratings Report") & ~relabeled_frame["Table Number"].str.contains(r"\(", regex=True)
    if rating_mask.any():
        alias_series = relabeled_frame.loc[rating_mask, "Row Title"].astype(str).str.rsplit(":", n=1).str[-1].str.strip().str.upper()
        relabeled_frame.loc[rating_mask, "Table Number"] = relabeled_frame.loc[rating_mask, "Table Number"] + " (" + alias_series + ")"
    return relabeled_frame
def describe_unmapped_distribution_section(table_number, table_title, raw_entry, px_entry, in_blueprint, cov_df, no_counterpart):
    """Result record for a Standard section that is not on both sides (None when there is nothing to list): no raw counterpart = 'N/A - no counterpart' (the reasons come from the Blueprint coverage table), a mapped section missing from the PLEXOS output = FAIL."""
    if raw_entry is None:
        if px_entry is None and not in_blueprint:
            return None
        reasons = cov_df[(cov_df["Table"] == table_number) & (cov_df["Status"] != "DUPLICATE BLUEPRINT ROW - ignored")] if "Table" in cov_df.columns else pd.DataFrame()
        note = "; ".join(sorted(set(reasons["Status"] + ": " + reasons["Note"]))) if len(reasons) > 0 else "Section has no raw counterpart (no raw measure for it in the raw data)"
        return {"Report": "Standard Report", "Table Number": table_number, "Table Title": table_title, "Section Status": "N/A - " + no_counterpart, "Note": note}
    return {"Report": "Standard Report", "Table Number": table_number, "Table Title": table_title, "Section Status": "FAIL", "Note": "mapped section is missing from the PLEXOS output (the output mean and median cannot be calculated)"}
def pool_section_values(raw_df, px_df, monthly_cols, idonly_keys, table_number, table3_px_values):
    """Pool the monthly values of ALL rows of one section on each side (only the monthly columns). PLEXOS rows that match a structurally blank raw row (identifier only) are left out of the output pool; Table 3 PLEXOS = Primary + Secondary + Topping. Returns raw_array (rows x months), raw_values, px_values (finite values only), blank_rows_excluded."""
    blank_row_mask = normalize_series(px_df.iloc[:, 0].fillna("")).isin(idonly_keys).to_numpy()
    raw_array = raw_df[monthly_cols].apply(pd.to_numeric, errors="coerce").to_numpy(dtype=float)
    px_array = to_numeric_matrix(px_df[monthly_cols])
    if table_number == "3" and len(table3_px_values) > 0:
        occurrence_seen, rebuilt_rows = {}, []
        for position, text in enumerate(px_df.iloc[:, 0].fillna("").astype(str).str.strip().tolist()):
            key = normalize_text(text)
            occurrence = occurrence_seen.get(key, 0)
            occurrence_seen[key] = occurrence + 1
            if bool(blank_row_mask[position]):
                continue
            if key in table3_px_values and occurrence < len(table3_px_values[key]):
                rebuilt_rows.append(np.asarray(table3_px_values[key][occurrence], dtype=float))
            else:
                rebuilt_rows.append(px_array[position])
        px_pool_array = np.concatenate(rebuilt_rows) if len(rebuilt_rows) > 0 else np.array([])
    else:
        px_pool_array = px_array[~blank_row_mask].flatten()
    raw_pool_array = raw_array.flatten()
    return raw_array, raw_pool_array[np.isfinite(raw_pool_array)], px_pool_array[np.isfinite(px_pool_array)], int(blank_row_mask.sum())
def describe_distribution(values):
    """Mean, median, standard deviation (ddof=1), mean minus median, Pearson skewness = 3 x (mean - median) / standard deviation (0 when the pooled data is constant or a single value) and the skew direction (mean > median Right-Skewed, mean < median Left-Skewed). Returns mean, median, sd, mean_minus_median, skewness, direction."""
    n = len(values)
    mean_value = float(values.mean()) if n > 0 else np.nan
    median_value = float(np.median(values)) if n > 0 else np.nan
    sd_value = float(values.std(ddof=1)) if n > 1 else np.nan
    mean_minus_median = (mean_value - median_value) if (n > 0) else np.nan
    if n == 0:
        skewness = np.nan
    elif n == 1 or (pd.notna(sd_value) and sd_value <= 1e-12 * max(1.0, abs(mean_value))):
        skewness = 0.0
    else:
        skewness = 3.0 * (mean_value - median_value) / sd_value
    if n == 0:
        direction = "Unable to Evaluate"
    elif math.isclose(mean_value, median_value, rel_tol=1e-9, abs_tol=1e-12):
        direction = "Symmetric"
    elif mean_value > median_value:
        direction = "Right-Skewed"
    else:
        direction = "Left-Skewed"
    return mean_value, median_value, sd_value, mean_minus_median, skewness, direction
def build_distribution_entry(table_number, table_title, raw_array, px_row_count, blank_rows_excluded, monthly_cols, raw_values, px_values, skew_exceeds_threshold, material_threshold):
    """Result record of one mapped section: the pooled statistics of each side, the output-minus-raw mean-to-median difference, the skew divergence |output skewness - raw skewness|, the material-divergence flag (greater than material_threshold), whether the skew direction changes and the section status."""
    entry = {"Report": "Standard Report", "Table Number": table_number, "Table Title": table_title, "Raw Rows Pooled": int((~np.isnan(raw_array)).any(axis=1).sum()), "PLEXOS Rows Pooled": px_row_count - blank_rows_excluded,
             "Structurally Blank Rows Excluded": blank_rows_excluded, "Monthly Columns Used": len(monthly_cols), "Raw Numeric Count": int(len(raw_values)), "PLEXOS Numeric Count": int(len(px_values))}
    side_stats = {}
    for side_label, side_values in (("Raw", raw_values), ("PLEXOS", px_values)):
        mean_value, median_value, sd_value, mean_minus_median, skewness, direction = describe_distribution(side_values)
        side_stats[side_label] = (mean_value, median_value, sd_value, mean_minus_median, skewness, direction)
        entry[f"{side_label} Section Mean"] = mean_value
        entry[f"{side_label} Section Median"] = median_value
        entry[f"{side_label} Mean Minus Median"] = mean_minus_median
        entry[f"{side_label} Section Standard Deviation"] = sd_value
        entry[f"{side_label} Pearson Skewness"] = skewness
        entry[f"{side_label} Skewness Exceeds 1"] = int(pd.notna(skewness) and abs(skewness) > skew_exceeds_threshold)
        entry[f"{side_label} Skew Direction"] = direction
    raw_skew, px_skew = side_stats["Raw"][4], side_stats["PLEXOS"][4]
    entry["Output Minus Raw Mean-to-Median Difference"] = (side_stats["PLEXOS"][3] - side_stats["Raw"][3]) if (pd.notna(side_stats["PLEXOS"][3]) and pd.notna(side_stats["Raw"][3])) else np.nan
    entry["Skew Divergence"] = abs(px_skew - raw_skew) if (pd.notna(raw_skew) and pd.notna(px_skew)) else np.nan
    entry["Material Skew Divergence"] = int(entry["Skew Divergence"] > material_threshold) if pd.notna(entry["Skew Divergence"]) else np.nan
    entry["Direction Changes"] = int(side_stats["Raw"][5] != side_stats["PLEXOS"][5])
    entry["Unable to Evaluate"] = int(pd.isna(raw_skew) or pd.isna(px_skew))
    entry["Section Status"] = "EVALUATED" if entry["Unable to Evaluate"] == 0 else "FAIL"
    entry["Note"] = "" if entry["Unable to Evaluate"] == 0 else "no numeric monthly values on one side, so the relationship cannot be compared"
    return entry
def split_distribution_results(mean_median_results):
    """Split the results. Returns evaluated (compared sections), unmapped_sections (N/A: no counterpart) and failed_sections."""
    return (mean_median_results[mean_median_results["Section Status"] == "EVALUATED"], mean_median_results[mean_median_results["Section Status"].astype(str).str.startswith("N/A")], mean_median_results[mean_median_results["Section Status"] == "FAIL"])
def print_section_columns(frame, columns):
    """Print the listed columns of a results table (nothing for an empty table)."""
    if not frame.empty:
        print(frame[columns].to_string(index=False))
def find_missing_statistics(evaluated, failed_sections, columns):
    """Step 2: the failed sections plus the compared sections that miss any of the listed statistics."""
    missing = failed_sections.copy()
    if not evaluated.empty:
        missing = pd.concat([missing, evaluated[evaluated[columns].isna().any(axis=1)]])
    return missing
def check_mean_minus_median(evaluated):
    """Step 5: the mean-to-median difference is present on both sides of every compared section and equals mean minus median. Returns step5_fail (sections with a missing difference), recomputed_ok."""
    step5_fail = evaluated[evaluated[["Raw Mean Minus Median", "PLEXOS Mean Minus Median"]].isna().any(axis=1)] if not evaluated.empty else evaluated
    recomputed_ok = bool(evaluated.empty or (np.allclose((evaluated["Raw Section Mean"] - evaluated["Raw Section Median"]).to_numpy(dtype=float), evaluated["Raw Mean Minus Median"].to_numpy(dtype=float), rtol=1e-3, atol=1e-3)
                                              and np.allclose((evaluated["PLEXOS Section Mean"] - evaluated["PLEXOS Section Median"]).to_numpy(dtype=float), evaluated["PLEXOS Mean Minus Median"].to_numpy(dtype=float), rtol=1e-3, atol=1e-3)))
    return step5_fail, recomputed_ok
def check_skew_direction(evaluated):
    """Step 8: a direction is identified on both sides of every compared section, and mean > median is Right-Skewed / mean < median is Left-Skewed. Returns direction_ok, direction_consistent."""
    valid_directions = {"Right-Skewed", "Left-Skewed", "Symmetric"}
    direction_ok = bool(evaluated.empty or (evaluated["Raw Skew Direction"].isin(valid_directions).all() and evaluated["PLEXOS Skew Direction"].isin(valid_directions).all()))
    direction_consistent = True
    for _, r in evaluated.iterrows():
        for side_label in ("Raw", "PLEXOS"):
            mean_value, median_value, direction = r[f"{side_label} Section Mean"], r[f"{side_label} Section Median"], r[f"{side_label} Skew Direction"]
            if mean_value > median_value and not math.isclose(mean_value, median_value, rel_tol=1e-9, abs_tol=1e-12) and direction != "Right-Skewed":
                direction_consistent = False
            if mean_value < median_value and not math.isclose(mean_value, median_value, rel_tol=1e-9, abs_tol=1e-12) and direction != "Left-Skewed":
                direction_consistent = False
    return direction_ok, direction_consistent
def build_distribution_exports(results_folder, mean_median_results):
    """The exports of Step 9: label -> (path, table, abnormal_only). Every section, the review / exception report (sections flagged for material divergence or with a skewness above 1 on either side) and the section status (incl. the Ratings N/A sections)."""
    results_folder = Path(results_folder)
    review_mask = (mean_median_results["Material Skew Divergence"] == 1) | (mean_median_results["Raw Skewness Exceeds 1"] == 1) | (mean_median_results["PLEXOS Skewness Exceeds 1"] == 1) if "Material Skew Divergence" in mean_median_results.columns else pd.Series(False, index=mean_median_results.index)
    return {"Comparison report (every section)": (results_folder / "PlexOS_3_03E_Abnormalities_MeanMedian_Comparison.csv", mean_median_results, False),
            "Review / exception report (flagged sections)": (results_folder / "PlexOS_3_03E_Abnormalities_MeanMedian.csv", mean_median_results[review_mask.fillna(False)], False),
            "Section status (incl. Ratings N/A)": (results_folder / "PlexOS_3_03E_Section_Status.csv", mean_median_results[["Report", "Table Number", "Table Title", "Section Status", "Note"]], False)}
def load_reference_results(results_folder, required_columns, session_results=None):
    """The PlexOS-3.03C results table this block reconciles to: the DataFrame 3.03C left in this session, else the CSV 3.03C wrote to the results folder (the first one that has every needed column). Returns reference_results (None when not found), reference_source, reference_problem."""
    candidates = []
    if isinstance(session_results, pd.DataFrame) and len(session_results) > 0:
        candidates.append(("magnitude_results (PlexOS-3.03C, this session)", session_results.copy()))
    csv_path = Path(results_folder) / "PlexOS_3_03C_Magnitude_Results.csv"
    if csv_path.is_file() and csv_path.stat().st_size > 5:
        candidates.append((str(csv_path), pd.read_csv(csv_path, dtype={"Table Number": str})))
    problem = ""
    for source, frame in candidates:
        missing_columns = [c for c in required_columns if c not in frame.columns]
        if len(missing_columns) == 0:
            return frame, source, problem
        problem = f"{source} lacks the column(s) {missing_columns}: it is not the PlexOS-3.03C results table this block reconciles to"
    return None, "", problem
def strip_section_columns(data):
    """Shallow copy of a section table whose column labels are stripped text (the 3.03C table itself is left untouched)."""
    stripped = data.copy(deep=False)
    stripped.columns = stripped.columns.astype(str).str.strip()
    return stripped
def build_histogram_section_record(report_name, table_number, table_title, status, note):
    """One section-status record of the histogram block (GENERATED, FAIL or N/A - no counterpart)."""
    return {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Histogram Status": status, "Note": note}
def describe_unmapped_histogram_section(report_name, table_number, table_title, raw_entry, px_entry, no_counterpart, ratings_no_raw_reason):
    """Section-status record of a section that is not on both sides (None when there is nothing to list): no raw counterpart = 'N/A - no counterpart' (not a failure), a mapped section missing from the PLEXOS output = FAIL."""
    if raw_entry is None:
        if px_entry is None:
            return None
        return build_histogram_section_record(report_name, table_number, table_title, "N/A - " + no_counterpart, ratings_no_raw_reason if report_name == "Ratings Report" else "Section has no raw counterpart (no raw measure for it in the raw data)")
    return build_histogram_section_record(report_name, table_number, table_title, "FAIL", "mapped section is missing from the PLEXOS output, so there is no output distribution to overlay")
def build_excluded_row_record(report_name, table_number, table_title, row_title, raw_names, reason, occurrences):
    """One record of a row that is left out of the comparison (listed on the Excluded_Rows sheet)."""
    return {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Row Title": row_title, "Raw Data Name(s)": raw_names, "Left Out Because": reason, "Occurrences": occurrences}
def find_unpaired_rows(report_name, table_number, table_title, raw_positions, px_positions, raw_display, px_display, raw_name_lookup):
    """Rows left out of the pools because they cannot be paired: rows only in the raw data, rows only in PLEXOS and titles whose occurrence counts differ (only the first min(raw, PLEXOS) are paired). Returns a list of excluded-row records."""
    unpaired = []
    for key in sorted(set(raw_positions) - set(px_positions)):
        unpaired.append(build_excluded_row_record(report_name, table_number, table_title, raw_display[key], raw_name_lookup.get(key, ""), "Only in the raw data (no PLEXOS row with this title)", len(raw_positions[key])))
    for key in sorted(set(px_positions) - set(raw_positions)):
        unpaired.append(build_excluded_row_record(report_name, table_number, table_title, px_display[key], "", "Only in PLEXOS (no raw row with this title)", len(px_positions[key])))
    for key in sorted(set(raw_positions) & set(px_positions)):
        if len(raw_positions[key]) != len(px_positions[key]):
            unpaired.append(build_excluded_row_record(report_name, table_number, table_title, px_display[key], raw_name_lookup.get(key, ""),
                                                      f"Occurrence count differs (raw x{len(raw_positions[key])}, PLEXOS x{len(px_positions[key])}): only the first {min(len(raw_positions[key]), len(px_positions[key]))} are paired",
                                                      abs(len(raw_positions[key]) - len(px_positions[key]))))
    return unpaired
def build_box_jobs(scope, report_name, table_number, table_title, row_title, occurrence, raw_values, px_values):
    """The four box-and-whisker jobs of one set of values (Raw / PLEXOS x 'All values (zeros included)' / 'Non-zero values'); scope is 'Section' or 'Row'."""
    box_jobs = []
    for basis in ("All values (zeros included)", "Non-zero values"):
        for source, values in (("Raw", raw_values), ("PLEXOS", px_values)):
            box_jobs.append({"Scope": scope, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Row Title": row_title, "Occurrence": occurrence,
                             "Basis": basis, "Source": source, "values": values if basis.startswith("All") else values[values != 0]})
    return box_jobs
def summarize_values(values):
    """(mean, minimum, maximum, median) of the readable values of one row, all NaN when there are none."""
    if values.size == 0:
        return np.nan, np.nan, np.nan, np.nan
    return float(values.mean()), float(values.min()), float(values.max()), float(np.median(values))
def pair_matched_rows(report_name, table_number, table_title, common_keys, raw_positions, px_positions, raw_matrix, px_matrix, raw_row_of, px_row_of, px_display, raw_name_lookup, table3_px_values):
    """Pair the rows present on both sides, occurrence by occurrence (Table 3 PLEXOS = Primary + Secondary + Topping, as in PlexOS-3.03C). A raw row without any value is left out as 'structurally blank'. Returns raw_chunks, px_chunks (the readable values of every matched row), row_records (per row statistics for the reconciliation with 3.03C), row_box_jobs and blank_rows (excluded-row records)."""
    raw_chunks, px_chunks, row_records, row_box_jobs, blank_rows = [], [], [], [], []
    for key in common_keys:
        for occurrence in range(min(len(raw_positions[key]), len(px_positions[key]))):
            raw_series_full = raw_matrix[raw_row_of[raw_positions[key][occurrence]]]
            raw_row_values = raw_series_full[np.isfinite(raw_series_full)]
            if report_name == "Standard Report" and table_number == "3" and key in table3_px_values and occurrence < len(table3_px_values[key]):
                px_series_full = np.asarray(table3_px_values[key][occurrence], dtype=float)
            else:
                px_series_full = px_matrix[px_row_of[px_positions[key][occurrence]]]
            px_row_values = px_series_full[np.isfinite(px_series_full)]
            if raw_row_values.size == 0:
                blank_rows.append(build_excluded_row_record(report_name, table_number, table_title, px_display[key], raw_name_lookup.get(key, ""), "Structurally blank raw row (no raw measure): not applicable", 1))
                continue
            raw_chunks.append(raw_row_values)
            px_chunks.append(px_row_values)
            raw_mean, raw_minimum, raw_maximum, raw_median = summarize_values(raw_row_values)
            px_mean, px_minimum, px_maximum, px_median = summarize_values(px_row_values)
            row_records.append({"Report": report_name, "Table Number": str(table_number), "Row Key": key, "Occurrence": occurrence + 1, "Raw Mean": raw_mean, "PLEXOS Mean": px_mean, "Raw Minimum": raw_minimum, "PLEXOS Minimum": px_minimum,
                                "Raw Maximum": raw_maximum, "PLEXOS Maximum": px_maximum, "Raw Median": raw_median, "PLEXOS Median": px_median, "Raw Numeric Count": int(raw_row_values.size), "PLEXOS Numeric Count": int(px_row_values.size)})
            row_box_jobs.extend(build_box_jobs("Row", report_name, table_number, table_title, px_display[key], occurrence + 1, raw_row_values, px_row_values))
    return raw_chunks, px_chunks, row_records, row_box_jobs, blank_rows
def build_histogram_record(report_name, table_number, table_title, matched_rows, rows_only_in_raw, rows_only_in_px, raw_values, px_values, output_dir, bins):
    """Draw and save the histogram of one section (raw and PLEXOS bars on shared bin edges over the combined non-zero range, mean / median markers, zeros disclosed in a note) and return its manifest record: counts, zeros, means / medians, bin range, bar totals, whether the plotted edges and totals check out, markers drawn and the PNG path."""
    raw_mean, raw_median = describe_distribution(raw_values)[:2]
    px_mean, px_median = describe_distribution(px_values)[:2]
    raw_zero_count, px_zero_count = int((raw_values == 0).sum()), int((px_values == 0).sum())
    raw_nonzero, px_nonzero = raw_values[raw_values != 0], px_values[px_values != 0]
    combined_nonzero = np.concatenate([raw_nonzero, px_nonzero])
    if len(combined_nonzero) == 0:
        combined_min, combined_max = -0.5, 0.5
    else:
        combined_min, combined_max = float(combined_nonzero.min()), float(combined_nonzero.max())
        if combined_min == combined_max:
            combined_min -= 0.5
            combined_max += 0.5
    bin_edges = np.linspace(combined_min, combined_max, bins + 1)
    raw_bin_counts, _ = np.histogram(raw_nonzero, bins=bin_edges)
    px_bin_counts, _ = np.histogram(px_nonzero, bins=bin_edges)
    hist_figure = Figure(figsize=(10, 6))
    hist_axes = hist_figure.add_subplot()
    raw_plot_counts, raw_plot_edges, _ = hist_axes.hist(raw_nonzero, bins=bin_edges, alpha=0.5, label=f"Raw Data (n={len(raw_values)})", color="tab:blue", edgecolor="black")
    px_plot_counts, px_plot_edges, _ = hist_axes.hist(px_nonzero, bins=bin_edges, alpha=0.5, label=f"PLEXOS (n={len(px_values)})", color="tab:orange", edgecolor="black")
    markers_drawn = 0
    for marker_value, marker_color, marker_style, marker_label in ((raw_mean, "tab:blue", "solid", f"Raw Data Mean ({raw_mean:.3g})"), (raw_median, "tab:blue", "dashed", f"Raw Data Median ({raw_median:.3g})"),
                                                                   (px_mean, "tab:orange", "solid", f"PLEXOS Mean ({px_mean:.3g})"), (px_median, "tab:orange", "dashed", f"PLEXOS Median ({px_median:.3g})")):
        if pd.notna(marker_value):
            hist_axes.axvline(marker_value, color=marker_color, linestyle=marker_style, linewidth=2, label=marker_label)
            markers_drawn += 1
    hist_axes.set_title(f"{report_name} -- Table {table_number}: {table_title}  (matched rows: {matched_rows})")
    hist_axes.set_xlabel("Monthly Value (zeros excluded from bars -- see note)")
    hist_axes.set_ylabel("Frequency")
    hist_axes.legend(fontsize=8)
    hist_figure.text(0.5, 0.01, f"Zero values excluded from bars -- Raw Data: {raw_zero_count} | PLEXOS: {px_zero_count}", ha="center", va="bottom", fontsize=9, style="italic")
    hist_figure.tight_layout(rect=[0, 0.03, 1, 1])
    histogram_path = Path(output_dir) / f"PlexOS_3_03E_Histogram_{report_name.replace(' ', '_')}_{str(table_number).replace(' ', '_').replace('/', '-')}.png"
    hist_figure.savefig(histogram_path)
    return {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Matched Rows": matched_rows, "Rows Only In Raw": rows_only_in_raw, "Rows Only In PLEXOS": rows_only_in_px,
            "Raw Count": len(raw_values), "PLEXOS Count": len(px_values), "Raw Zero Count": raw_zero_count, "PLEXOS Zero Count": px_zero_count, "Raw Non-Zero Count": len(raw_nonzero), "PLEXOS Non-Zero Count": len(px_nonzero),
            "Raw Mean": raw_mean, "Raw Median": raw_median, "PLEXOS Mean": px_mean, "PLEXOS Median": px_median,
            "Mean Ratio (Raw / PLEXOS)": (raw_mean / px_mean) if (pd.notna(px_mean) and abs(px_mean) > 1e-9) else np.nan, "Bins": bins, "Bin Min": combined_min, "Bin Max": combined_max,
            "Raw Bar Total": int(raw_bin_counts.sum()), "PLEXOS Bar Total": int(px_bin_counts.sum()),
            "Plotted Bin Edges Identical": bool(np.array_equal(raw_plot_edges, px_plot_edges) and np.array_equal(raw_plot_edges, bin_edges)),
            "Plotted Bar Totals Match Counts": bool(int(raw_plot_counts.sum()) == len(raw_nonzero) and int(px_plot_counts.sum()) == len(px_nonzero)), "Markers Drawn": markers_drawn, "Histogram Path": str(histogram_path)}
def reconcile_with_reference(block_rows_frame, reference_results, rtol, atol):
    """Row-by-row reconciliation of this block's per-row statistics with the PlexOS-3.03C results (same report, table, row title and occurrence): rows in both / only in one, the minimum / maximum / mean / median agreement within the tolerance and the raw and PLEXOS mean ratios. Returns the comparison table (empty when there is nothing to compare)."""
    if reference_results is None or block_rows_frame.empty:
        return pd.DataFrame()
    reference_frame = reference_results.copy()
    reference_frame["Table Number"] = reference_frame["Table Number"].astype(str)
    reference_frame["Row Key"] = reference_frame["Row Title"].map(normalize_text)
    reference_frame["Occurrence"] = pd.to_numeric(reference_frame["Occurrence"], errors="coerce").fillna(1).astype(int)
    reference_columns = ["Report", "Table Number", "Row Key", "Occurrence", "Raw Mean", "PLEXOS Mean", "Raw Minimum", "PLEXOS Minimum", "Raw Maximum", "PLEXOS Maximum", "Raw Median", "PLEXOS Median", "Raw Numeric Count", "PLEXOS Numeric Count"]
    reference_frame = reference_frame[reference_columns].rename(columns={c: f"3.03C {c}" for c in reference_columns[4:]})
    reference_compare = block_rows_frame.merge(reference_frame, on=["Report", "Table Number", "Row Key", "Occurrence"], how="outer", indicator=True)
    reference_compare["Row Status"] = reference_compare["_merge"].map({"both": "in both", "left_only": "only in this block (not in 3.03C)", "right_only": "only in 3.03C (not in this block)"})
    reference_compare["Statistics Differ"] = False
    for statistic_column in ("Raw Mean", "PLEXOS Mean", "Raw Minimum", "PLEXOS Minimum", "Raw Maximum", "PLEXOS Maximum", "Raw Median", "PLEXOS Median"):
        statistic_equal = np.isclose(reference_compare[statistic_column].astype(float), reference_compare[f"3.03C {statistic_column}"].astype(float), rtol=rtol, atol=atol, equal_nan=True)
        reference_compare[f"{statistic_column} Agrees"] = statistic_equal
        reference_compare["Statistics Differ"] = reference_compare["Statistics Differ"] | (~statistic_equal & (reference_compare["_merge"] == "both"))
    reference_compare["Raw Mean Ratio (this block / 3.03C)"] = reference_compare["Raw Mean"].astype(float) / reference_compare["3.03C Raw Mean"].astype(float).replace(0, np.nan)
    reference_compare["PLEXOS Mean Ratio (this block / 3.03C)"] = reference_compare["PLEXOS Mean"].astype(float) / reference_compare["3.03C PLEXOS Mean"].astype(float).replace(0, np.nan)
    reference_compare["Row Agrees With 3.03C"] = (reference_compare["_merge"] == "both") & (~reference_compare["Statistics Differ"])
    return reference_compare
def check_pooled_means_against_reference(hist_manifest, reference_results, rtol, atol):
    """Step H5: four mean / median markers are drawn on every histogram and the pooled raw and PLEXOS means equal the means of the 3.03C rows of the section (weighted by their number of values). Returns problems, reconciled_sections."""
    problems, reconciled_sections = [], 0
    for _, r in hist_manifest.iterrows():
        if r["Markers Drawn"] != 4:
            problems.append(f"{r['Report']} / {r['Table Number']}: {int(r['Markers Drawn'])} of 4 mean/median markers drawn")
        if reference_results is None:
            continue
        reference_rows = reference_results[(reference_results["Report"] == r["Report"]) & (reference_results["Table Number"].astype(str) == str(r["Table Number"]))]
        if reference_rows.empty:
            problems.append(f"{r['Report']} / {r['Table Number']}: no 3.03C rows to reconcile the pooled mean with")
            continue
        reference_raw_mean = float(np.average(reference_rows["Raw Mean"].astype(float), weights=reference_rows["Raw Numeric Count"].astype(float)))
        px_weights = reference_rows["PLEXOS Numeric Count"].astype(float)
        reference_px_mean = float(np.average(reference_rows["PLEXOS Mean"].astype(float), weights=px_weights)) if px_weights.sum() > 0 else np.nan
        for label, histogram_value, reference_value in (("Raw mean", r["Raw Mean"], reference_raw_mean), ("PLEXOS mean", r["PLEXOS Mean"], reference_px_mean)):
            if not np.isclose(histogram_value, reference_value, rtol=rtol, atol=atol, equal_nan=True):
                ratio_text = f" ({histogram_value / reference_value:.3f} x the 3.03C value)" if (pd.notna(reference_value) and abs(reference_value) > 1e-9) else ""
                problems.append(f"{r['Report']} / {r['Table Number']}: {label} {histogram_value:.5g} differs from the 3.03C pooled value {reference_value:.5g}{ratio_text}")
        reconciled_sections += 1
    return problems, reconciled_sections
def count_sections_with_different_means(hist_manifest, section_results):
    """Information only: how many sections have a PlexOS-3.03E section mean that differs from this block's matched-row mean."""
    differing = 0
    for _, r in hist_manifest.iterrows():
        section_rows = section_results[(section_results["Report"] == r["Report"]) & (section_results["Table Number"].astype(str) == str(r["Table Number"]))]
        if not section_rows.empty and not (np.isclose(r["Raw Mean"], section_rows.iloc[0]["Raw Section Mean"], rtol=1e-3, atol=1e-3, equal_nan=True) and np.isclose(r["PLEXOS Mean"], section_rows.iloc[0]["PLEXOS Section Mean"], rtol=1e-3, atol=1e-3, equal_nan=True)):
            differing += 1
    return differing
def verify_png_files(image_paths):
    """Step H7: every histogram file exists and is a valid, non-empty PNG (the 8-byte signature is checked). Returns the problems."""
    problems = []
    for image_path in image_paths:
        image_path = Path(image_path)
        if not image_path.is_file():
            problems.append(f"{image_path.name}: file not found")
            continue
        with open(image_path, "rb") as image_file:
            image_head = image_file.read(8)
        if len(image_head) == 0 or image_head != b"\x89PNG\r\n\x1a\n":
            problems.append(f"{image_path.name}: not a valid, non-empty PNG")
    return problems
def compute_box_statistics(box_jobs, whisker_multiplier, box_stat_names):
    """Box-and-whisker statistics of every job: N, zeros, minimum, Q1 / median / Q3 (linear interpolation = Excel QUARTILE.INC), IQR, whiskers (the extreme value inside the Tukey fences, never inside the box), maximum, mean and the outlier counts. Returns one row per job."""
    box_stat_rows = []
    for box_job in box_jobs:
        box_values = box_job["values"]
        box_record = {key: value for key, value in box_job.items() if key != "values"}
        box_record["N Values"] = int(box_values.size)
        box_record["N Zero Values"] = int((box_values == 0).sum())
        if box_values.size == 0:
            for stat_name in ("Minimum", "Q1", "Median", "Q3", "Maximum", "IQR", "Lower Whisker", "Upper Whisker", "Mean"):
                box_record[stat_name] = np.nan
            box_record["Outliers Below"] = 0
            box_record["Outliers Above"] = 0
        else:
            quartile_1, quartile_median, quartile_3 = np.percentile(box_values, [25, 50, 75])
            interquartile_range = quartile_3 - quartile_1
            lower_fence = quartile_1 - whisker_multiplier * interquartile_range
            upper_fence = quartile_3 + whisker_multiplier * interquartile_range
            inside_fences = box_values[(box_values >= lower_fence) & (box_values <= upper_fence)]
            box_record["Minimum"] = float(box_values.min())
            box_record["Q1"] = float(quartile_1)
            box_record["Median"] = float(quartile_median)
            box_record["Q3"] = float(quartile_3)
            box_record["Maximum"] = float(box_values.max())
            box_record["IQR"] = float(interquartile_range)
            box_record["Lower Whisker"] = float(min(inside_fences.min(), quartile_1)) if inside_fences.size > 0 else float(quartile_1)
            box_record["Upper Whisker"] = float(max(inside_fences.max(), quartile_3)) if inside_fences.size > 0 else float(quartile_3)
            box_record["Outliers Below"] = int((box_values < lower_fence).sum())
            box_record["Outliers Above"] = int((box_values > upper_fence).sum())
            box_record["Mean"] = float(box_values.mean())
        box_stat_rows.append(box_record)
    return pd.DataFrame(box_stat_rows, columns=["Scope", "Report", "Table Number", "Table Title", "Row Title", "Occurrence", "Basis", "Source"] + box_stat_names)
def build_wide_box_table(long_frame, key_columns, box_stat_names, include_differences):
    """Raw next to PLEXOS: one line per key (report / table / basis, plus row title and occurrence at row level) with every statistic of both sides, the median ratio and whether the Q1-Q3 boxes overlap; with include_differences also the PLEXOS - Raw difference of each statistic and the mean ratio."""
    wide_rows = []
    for group_keys, group in long_frame.groupby(key_columns, sort=False):
        raw_part = group[group["Source"] == "Raw"].iloc[0]
        px_part = group[group["Source"] == "PLEXOS"].iloc[0]
        wide_record = dict(zip(key_columns, group_keys))
        for stat_name in box_stat_names:
            wide_record[f"Raw {stat_name}"] = raw_part[stat_name]
            wide_record[f"PLEXOS {stat_name}"] = px_part[stat_name]
            if include_differences and stat_name not in ("N Values", "N Zero Values"):
                wide_record[f"{stat_name} Difference (PLEXOS - Raw)"] = px_part[stat_name] - raw_part[stat_name]
        wide_record["Median Ratio (Raw / PLEXOS)"] = (raw_part["Median"] / px_part["Median"]) if (pd.notna(px_part["Median"]) and abs(px_part["Median"]) > 1e-9) else np.nan
        if include_differences:
            wide_record["Mean Ratio (Raw / PLEXOS)"] = (raw_part["Mean"] / px_part["Mean"]) if (pd.notna(px_part["Mean"]) and abs(px_part["Mean"]) > 1e-9) else np.nan
        wide_record["Boxes Overlap (Q1-Q3)"] = bool(pd.notna(raw_part["Q1"]) and pd.notna(px_part["Q1"]) and raw_part["Q1"] <= px_part["Q3"] and px_part["Q1"] <= raw_part["Q3"])
        wide_rows.append(wide_record)
    return pd.DataFrame(wide_rows)
def write_box_workbook(workbook_path, notes_rows, sheet_frames):
    """Write the box-and-whisker Excel workbook: a 'Notes' sheet followed by one formatted sheet per table of sheet_frames ({sheet name: DataFrame}): dark header, column widths, number formats, frozen panes and filters."""
    with pd.ExcelWriter(workbook_path, engine="openpyxl") as excel_writer:
        pd.DataFrame(notes_rows).to_excel(excel_writer, sheet_name="Notes", index=False, header=False)
        for sheet_name, sheet_frame in sheet_frames.items():
            sheet_frame.to_excel(excel_writer, sheet_name=sheet_name, index=False)
        for sheet_name, sheet in excel_writer.sheets.items():
            if sheet_name == "Notes":
                sheet.column_dimensions["A"].width = 18
                sheet.column_dimensions["B"].width = 140
                sheet["A1"].font = Font(bold=True, size=13)
                for note_row in range(2, len(notes_rows) + 1):
                    sheet.cell(row=note_row, column=1).font = Font(bold=True)
                    sheet.cell(row=note_row, column=2).alignment = Alignment(wrap_text=True, vertical="top")
                continue
            for cell in sheet[1]:
                cell.fill = PatternFill("solid", fgColor="1F3864")
                cell.font = Font(bold=True, color="FFFFFF")
                cell.alignment = Alignment(wrap_text=True, vertical="top")
            for column_index in range(1, sheet.max_column + 1):
                header_text = str(sheet.cell(row=1, column=column_index).value)
                sheet.column_dimensions[get_column_letter(column_index)].width = 46 if header_text in ("Table Title", "Row Title", "Left Out Because", "Raw Data Name(s)") else (26 if header_text == "Basis" else 15)
                if column_index > 4 and not header_text.endswith(("Overlap (Q1-Q3)",)) and header_text not in ("Source", "Left Out Because", "Raw Data Name(s)", "Row Title", "Table Title", "Occurrence", "Basis", "Occurrences"):
                    number_format = "#,##0" if any(token in header_text for token in ("N Values", "N Zero", "Outliers")) else "#,##0.00"
                    for data_row in range(2, sheet.max_row + 1):
                        sheet.cell(row=data_row, column=column_index).number_format = number_format
            sheet.freeze_panes = "E2" if sheet_name != "Excluded_Rows" else "A2"
            sheet.auto_filter.ref = sheet.dimensions
def check_box_files_written(box_files):
    """Step H9: every exported file exists and is not empty. Returns the problems."""
    return [f"{box_file.name}: not written or empty" for box_file in box_files if not box_file.is_file() or box_file.stat().st_size == 0]
def read_csvs_or_empty(csv_paths):
    """Read exported CSV files back (Table Number as text). An export with no data lines is a legitimate empty file: it reads back as an empty table instead of raising EmptyDataError. Returns one table per path."""
    frames = []
    for csv_path in csv_paths:
        try:
            frames.append(pd.read_csv(csv_path, dtype={"Table Number": str}) if Path(csv_path).is_file() else pd.DataFrame())
        except pd.errors.EmptyDataError:
            frames.append(pd.DataFrame())
    return frames
def check_box_ordering(section_long, row_long):
    """Step H9: every box is ordered minimum <= lower whisker <= Q1 <= median <= Q3 <= upper whisker <= maximum (section and row level). Returns the problems."""
    problems = []
    for scope_label, scope_frame in (("section", section_long), ("row", row_long)):
        populated = scope_frame[scope_frame["N Values"] > 0]
        ordering_ok = ((populated["Minimum"] <= populated["Lower Whisker"] + 1e-9) & (populated["Lower Whisker"] <= populated["Q1"] + 1e-9) & (populated["Q1"] <= populated["Median"] + 1e-9)
                       & (populated["Median"] <= populated["Q3"] + 1e-9) & (populated["Q3"] <= populated["Upper Whisker"] + 1e-9) & (populated["Upper Whisker"] <= populated["Maximum"] + 1e-9))
        if not bool(ordering_ok.all()):
            problems.append(f"{int((~ordering_ok).sum())} {scope_label} box(es) are not ordered min <= lower whisker <= Q1 <= median <= Q3 <= upper whisker <= max")
    return problems
def recompute_section_boxes(section_pools, readback_section, whisker_multiplier):
    """Independent recalculation of every section box with pandas (a different code path from the numpy percentile), compared with the values READ BACK from the CSV. Returns boxes_checked, differences."""
    checked, differences = 0, []
    for (pool_report, pool_table), (pool_raw, pool_px) in section_pools.items():
        for pool_source, pool_values in (("Raw", pool_raw), ("PLEXOS", pool_px)):
            for pool_basis, basis_values in (("All values (zeros included)", pool_values), ("Non-zero values", pool_values[pool_values != 0])):
                read_line = readback_section[(readback_section["Report"] == pool_report) & (readback_section["Table Number"] == pool_table) & (readback_section["Basis"] == pool_basis) & (readback_section["Source"] == pool_source)]
                if len(read_line) != 1:
                    differences.append(f"{pool_report} / {pool_table} / {pool_basis} / {pool_source}: {len(read_line)} line(s) in the CSV")
                    continue
                if basis_values.size == 0:
                    checked += 1
                    continue
                pandas_series = pd.Series(basis_values)
                q1_pandas, q3_pandas = pandas_series.quantile(0.25), pandas_series.quantile(0.75)
                fence_low, fence_high = q1_pandas - whisker_multiplier * (q3_pandas - q1_pandas), q3_pandas + whisker_multiplier * (q3_pandas - q1_pandas)
                pandas_inside = pandas_series[(pandas_series >= fence_low) & (pandas_series <= fence_high)]
                expected_values = {"Minimum": pandas_series.min(), "Q1": q1_pandas, "Median": pandas_series.median(), "Q3": q3_pandas, "Maximum": pandas_series.max(), "Mean": pandas_series.mean(),
                                   "Lower Whisker": min(pandas_inside.min(), q1_pandas) if len(pandas_inside) else q1_pandas, "Upper Whisker": max(pandas_inside.max(), q3_pandas) if len(pandas_inside) else q3_pandas,
                                   "Outliers Below": int((pandas_series < fence_low).sum()), "Outliers Above": int((pandas_series > fence_high).sum()), "N Values": int(len(pandas_series))}
                for stat_name, expected_value in expected_values.items():
                    if not np.isclose(float(read_line.iloc[0][stat_name]), float(expected_value), rtol=1e-9, atol=1e-9):
                        differences.append(f"{pool_report} / {pool_table} / {pool_basis} / {pool_source}: {stat_name} {read_line.iloc[0][stat_name]} vs independent {expected_value}")
                checked += 1
    return checked, differences
def read_workbook_sheet_names(workbook_path):
    """Sheet names of a written workbook (it must open). Returns sheet_names, problems."""
    try:
        workbook_check = openpyxl.load_workbook(workbook_path, read_only=True)
        sheet_names = list(workbook_check.sheetnames)
        workbook_check.close()
        return sheet_names, []
    except Exception as workbook_error:
        return [], [f"{Path(workbook_path).name} could not be opened: {type(workbook_error).__name__}"]
def summarize_reference_comparison(reference_compare, rtol, double_count_band):
    """Step H10: print how the rows of this block agree with the PlexOS-3.03C results (rows in both / only in one / with differing statistics) and, for every table that does not agree, what the raw and PLEXOS mean ratios point to (raw values counted twice, a different raw measure, a different set of matched rows). Returns the problems and whether at least one row is in both."""
    only_in_block = reference_compare[reference_compare["_merge"] == "left_only"]
    only_in_reference = reference_compare[reference_compare["_merge"] == "right_only"]
    in_both = reference_compare[reference_compare["_merge"] == "both"]
    differing = in_both[in_both["Statistics Differ"]]
    print(f"  3.03C matched row occurrences: {len(reference_compare) - len(only_in_block)} | this block: {len(reference_compare) - len(only_in_reference)} | in both: {len(in_both)}")
    print(f"  Rows only in this block: {len(only_in_block)} | rows only in 3.03C: {len(only_in_reference)} | rows whose statistics differ: {len(differing)} (tolerance {rtol:g} relative; 3.03C rounds to 5 significant figures)")
    problems = []
    if len(only_in_block) > 0:
        problems.append(f"{len(only_in_block)} row(s) are in this block but not in 3.03C")
    if len(only_in_reference) > 0:
        problems.append(f"{len(only_in_reference)} row(s) are in 3.03C but not in this block")
    if len(differing) > 0:
        problems.append(f"{len(differing)} row(s) have a minimum / maximum / mean / median that differs from 3.03C")
    per_table_rows = []
    for table_label in pd.unique(reference_compare["Table Number"]):
        table_group = reference_compare[reference_compare["Table Number"] == table_label]
        per_table_rows.append({"Table Number": table_label, "rows 3.03C": int((table_group["_merge"] != "left_only").sum()), "rows block": int((table_group["_merge"] != "right_only").sum()),
                               "agree": int(table_group["Row Agrees With 3.03C"].sum()), "raw ratio": table_group["Raw Mean Ratio (this block / 3.03C)"].median(), "PLEXOS ratio": table_group["PLEXOS Mean Ratio (this block / 3.03C)"].median()})
    per_table = pd.DataFrame(per_table_rows).set_index("Table Number")
    bad_tables = per_table[(per_table["agree"] != per_table["rows 3.03C"]) | (per_table["rows 3.03C"] != per_table["rows block"])]
    for table_label, table_row in bad_tables.head(25).iterrows():
        diagnosis = []
        if pd.notna(table_row["raw ratio"]) and double_count_band[0] <= table_row["raw ratio"] <= double_count_band[1]:
            diagnosis.append("the raw values are about 2x the 3.03C raw values: Timeslice rows (All Periods + Off-Peak + On-Peak) are being added up")
        elif pd.notna(table_row["raw ratio"]) and abs(table_row["raw ratio"] - 1) > rtol:
            diagnosis.append(f"the raw values are {table_row['raw ratio']:.3f} x the 3.03C raw values (check the raw measure: Total System Cost = Fuel + Start-up + VO&M only, no FO&M)")
        if table_row["rows block"] != table_row["rows 3.03C"]:
            diagnosis.append("the set of matched rows differs (check the maptable_ entries and the group definitions, e.g. the Thermal group must include ST_Gas)")
        if pd.notna(table_row["PLEXOS ratio"]) and abs(table_row["PLEXOS ratio"] - 1) > rtol:
            diagnosis.append(f"the PLEXOS values are {table_row['PLEXOS ratio']:.3f} x the 3.03C PLEXOS values")
        print(f"    Table {table_label}: {int(table_row['agree'])} of {int(table_row['rows 3.03C'])} rows agree ({int(table_row['rows block'])} rows in this block) -- " + ("; ".join(diagnosis) if diagnosis else "statistics differ"))
    if len(bad_tables) > 25:
        print(f"    ... and {len(bad_tables) - 25} more table(s)")
    return problems, len(in_both) > 0
################################################################################################################################################################################
#3.04
################################################################################################################################################################################
def find_empty_source_reports(sr_path, rr_path, results_folder, defined_sr_path="", defined_rr_path=""):
    """Step 5a: locate the Standard / Ratings reports generated from an EMPTY source dataset. A path already defined in the session is used when the file still exists, else the folders of the two reports and the results folder are searched for a .csv whose name contains 'empty' plus 'standard' / 'rating' (the real reports and this suite's own output files are never picked; the newest match wins). Prints one line per report. Returns empty_sr_path, empty_rr_path ('' when none)."""
    search_folders = []
    for candidate_folder in (Path(sr_path).parent, Path(rr_path).parent, Path(results_folder)):
        if candidate_folder.is_dir() and candidate_folder.resolve() not in [f.resolve() for f in search_folders]:
            search_folders.append(candidate_folder)
    real_report_paths = {str(Path(sr_path).resolve()).lower(), str(Path(rr_path).resolve()).lower()}
    chosen = {}
    for optional_name, must_contain, defined_path in (("empty_sr_path", "standard", defined_sr_path), ("empty_rr_path", "rating", defined_rr_path)):
        chosen_path = str(defined_path or "").strip().strip('"').strip("'")
        if chosen_path != "" and not Path(chosen_path).is_file():
            print(f"  {optional_name}: '{chosen_path}' no longer exists - searching again")
            chosen_path = ""
        chosen_how = "defined in the session" if chosen_path != "" else ""
        if chosen_path == "":
            found_files = []
            for search_folder in search_folders:
                for found_file in search_folder.glob("*.csv"):
                    name_lower = found_file.name.lower()
                    if "empty" in name_lower and must_contain in name_lower and not name_lower.startswith("plexos_3_0") and str(found_file.resolve()).lower() not in real_report_paths:
                        found_files.append(found_file)
            if len(found_files) > 0:
                chosen_path = str(max(found_files, key=lambda f: f.stat().st_mtime))
                chosen_how = f"found automatically ({len(found_files)} match(es); newest used)"
        print(f"  {optional_name}: {chosen_path if chosen_path != '' else '(none found - Step 5a skipped)'}{'  [' + chosen_how + ']' if chosen_how else ''}")
        chosen[optional_name] = chosen_path
    return chosen["empty_sr_path"], chosen["empty_rr_path"]
def text_to_numeric_matrix(frame):
    """Every field of a table as a float matrix (rows x columns) with the PlexOS-3.04 reading rule: text with the "," thousands separator removed -> number; anything else (blank, text, "$" or "%" signs) = NaN."""
    return pd.to_numeric(pd.Series(frame.to_numpy().ravel()).astype(str).str.replace(",", "", regex=False), errors="coerce").to_numpy(dtype=float).reshape(frame.shape)
def remove_structural_rows_keep_titled_data(reports):
    """Remove the structural rows from the PLEXOS side of both reports: 'Total' rows, blank-title spacer rows and indented (Primary) / (Secondary) / (Startup) / (Topping) sub-rows. Unlike remove_plexos_structural_rows, a blank-title row that carries numeric values is a DATA row with a NULL row title: it is kept and listed. Returns structural_rows_removed ({(report, table): count}) and blank_title_rows_with_data (one record per kept row)."""
    structural_rows_removed, blank_title_rows_with_data = {}, []
    for report_name, report_config in reports.items():
        for table_number, table in report_config["PLEXOS_tables"].items():
            data = table["data"]
            if len(data.columns) == 0:
                continue
            label_norm = data.iloc[:, 0].fillna("").astype(str).str.replace(r"\s+", " ", regex=True).str.strip().str.lower()
            value_block = data.iloc[:, 1:]
            if value_block.shape[1] > 0 and len(value_block) > 0:
                numeric_present = ~np.isnan(text_to_numeric_matrix(value_block))
            else:
                numeric_present = np.zeros(value_block.shape, dtype=bool)
            blank_with_data_array = (label_norm.to_numpy() == "") & numeric_present.any(axis=1)
            blank_with_data = pd.Series(blank_with_data_array, index=data.index)
            for row_offset in np.flatnonzero(blank_with_data_array).tolist():
                blank_title_rows_with_data.append({"Report": report_name, "Table Number": table_number, "Output Row Position": int(data.index[row_offset]) + 1, "Numeric Fields On The Row": int(numeric_present[row_offset].sum())})
            structural_mask = ((label_norm == "") & ~blank_with_data) | (label_norm == "total") | label_norm.str.startswith("(")
            structural_rows_removed[(report_name, table_number)] = int(structural_mask.sum())
            table["data"] = data[~structural_mask].reset_index(drop=True)
    return structural_rows_removed, blank_title_rows_with_data
def extract_blueprint_sections_keep_null(blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, in_scope_tables, class_to_raw, property_to_raw_column,
                                         derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """Same as extract_blueprint_sections (same arguments, same 11 results, same printed summary) with ONE difference needed by a population test: a (row, month) whose raw values are ALL blank stays NULL (sum with min_count=1) instead of becoming 0, so the populated-field counts of the raw side are exact. Returns extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys, cov_df, table_order, out_of_scope_tables, blueprint_titles."""
    extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys = {}, {}, {}, {}, {}, {}, {}
    coverage_rows, table_order, out_of_scope_tables, blueprint_titles, seen_specs = [], [], set(), {}, set()
    df_gen = raw_frames["df_gen"]
    parent_cat = df_gen[df_gen["Collection"] == "Generator"].drop_duplicates("Child Name").set_index("Child Name")["Category"].astype(str).str.strip().str.lower()
    raw_parts = {}
    for part_fkey, part_frame in raw_frames.items():
        for part_coll, part_rows in part_frame.groupby("Collection", sort=False):
            raw_parts[(part_fkey, part_coll)] = part_rows
    part_key_cache, group_mask_cache, id_str_cache, id_printed_cache, printed_row_cache, child_factor_cache = {}, {}, {}, {}, {}, {}
    for brow in blueprint.to_dict("records"):
        header = brow["Header"]
        tmatch = re.match(r"^\(\s*(\w+)\s*\)", header)
        tkey = tmatch.group(1).lower() if tmatch else header.lower()
        if tkey not in in_scope_tables:
            out_of_scope_tables.add(tkey)
            continue
        if tkey not in table_order:
            table_order.append(tkey)
            blueprint_titles[tkey] = name_map.get(re.sub(r"\s+", " ", header).strip().lower(), header)
        cls_in, grp_in, prop_in, pattern = brow["Class"], brow["Group"], brow["Property"], brow["Pattern"].lower()
        cls_l, grp_l = cls_in.lower(), grp_in.lower()
        unit_bp = brow["Unit"]
        sign = float(brow["Sign"]) if brow["Sign"] != "" else 1.0
        use_mean = brow["Rate"].strip().lower() in ("true", "1", "yes")
        cov = {"Table": tkey, "Class": cls_in, "Group": grp_in, "Property": prop_in, "Pattern": pattern, "Raw Column": "", "Status": "", "Note": ""}
        spec_id = (header, cls_l, grp_l, prop_in, pattern, unit_bp, sign)
        if spec_id in seen_specs:
            cov["Status"] = "DUPLICATE BLUEPRINT ROW - ignored"
            coverage_rows.append(cov)
            continue
        seen_specs.add(spec_id)
        if tkey in skip_tables:
            cov["Status"], cov["Note"] = "NO COUNTERPART - custom section", skip_tables[tkey]
            coverage_rows.append(cov)
            continue
        if pattern.startswith("daily"):
            cov["Status"], cov["Note"] = "NO COUNTERPART - daily pattern", "Raw workbook is monthly only"
            coverage_rows.append(cov)
            continue
        eff_cls, eff_prop = cls_l, prop_in
        if (tkey, cls_l, prop_in) in custom_overrides:
            eff_cls, eff_prop, cov["Note"] = custom_overrides[(tkey, cls_l, prop_in)]
        if eff_cls not in class_to_raw:
            cov["Status"], cov["Note"] = "NO COUNTERPART - class not in raw data", f"Class '{cls_in}' is not in the raw workbook"
            coverage_rows.append(cov)
            continue
        fkey, coll, id_col = class_to_raw[eff_cls]
        cats, gk = None, None
        if grp_l not in ("all", ""):
            gk = (cls_l, grp_l)
            if gk not in group_assets:
                gk = ("generator", grp_l)
            if gk not in group_assets:
                cov["Status"], cov["Note"] = "UNKNOWN GROUP", f"Class '{cls_in}' + Group '{grp_in}' is not defined on the Groups sheet"
                coverage_rows.append(cov)
                continue
            cats = group_assets[gk]
        printed_summary, generated = None, ""
        if pattern == "monthly-summary":
            gl = "all" if cats is None else group_label.get((cls_l, grp_l), group_label.get(("generator", grp_l), grp_in))
            generated = f"{cls_in}-{gl}-{prop_in}-Total"
            printed_summary = name_map.get(re.sub(r"\s+", " ", generated).strip().lower(), generated)
        derived_components = derived_measures.get((fkey, coll, eff_prop))
        raw_col = None if (eff_cls, eff_prop) in no_raw_notes else property_to_raw_column.get((fkey, coll), {}).get(eff_prop)
        if raw_col is None:
            note_text = no_raw_notes.get((eff_cls, eff_prop), f"No '{eff_prop}' column for {fkey} / {coll}")
            if printed_summary is not None:
                key_only = re.sub(r"\s+", " ", printed_summary).strip().lower()
                pv_only = pd.DataFrame(np.nan, index=[key_only], columns=month_labels)
                if tkey in extracted:
                    extracted[tkey] = pd.concat([extracted[tkey], pv_only])
                else:
                    extracted[tkey] = pv_only
                    extracted_display[tkey], extracted_names[tkey], extracted_raw_ids[tkey] = {}, {}, set()
                    extracted_idonly[tkey], extracted_rate[tkey] = set(), use_mean
                extracted_raw_ids[tkey].add(generated)
                extracted_display[tkey][key_only] = printed_summary
                extracted_names[tkey][key_only] = generated
                extracted_idonly[tkey].add(key_only)
                cov["Status"], cov["Note"] = "IDENTIFIER ONLY (no raw measure)", note_text + "; structurally blank raw row"
            else:
                cov["Status"], cov["Note"] = "NO COUNTERPART - no raw measure", note_text
            coverage_rows.append(cov)
            continue
        cov["Raw Column"] = raw_col
        needed_raw_columns = list(derived_components) if derived_components else [raw_col]
        missing_raw_columns = [c for c in needed_raw_columns if c not in raw_frames[fkey].columns]
        if missing_raw_columns:
            cov["Status"] = "NO COUNTERPART - raw column not in the workbook"
            cov["Note"] = f"The raw {fkey} sheet has no column {missing_raw_columns} (columns found: {list(raw_frames[fkey].columns)})"
            print(f"  WARNING: Blueprint row ({header} / {cls_in} / {grp_in} / {prop_in}) reads raw column(s) {missing_raw_columns} that are not on the raw sheet; the row is listed as 'raw column not in the workbook'")
            coverage_rows.append(cov)
            continue
        um = re.search(r"\(([^)]*)\)\s*$", raw_col)
        raw_unit = um.group(1).strip().lower() if um else "-"
        raw_unit = "hours" if raw_unit == "h" else raw_unit
        part = raw_parts.get((fkey, coll))
        if part is None:
            part = raw_frames[fkey].iloc[0:0]
        sub_mask = None
        if cats is not None:
            mask_key = (fkey, coll, gk)
            if mask_key not in group_mask_cache:
                pkey = (fkey, coll)
                if pkey not in part_key_cache:
                    if coll == "Generator.Fuels":
                        kc = part["Parent Name"].map(parent_cat).fillna("")
                        kn = part["Parent Name"].astype(str)
                    else:
                        kc = part["Category"].astype(str).str.strip().str.lower()
                        kn = part["Child Name"].astype(str)
                    part_key_cache[pkey] = (kc, kn.str.replace(r"\s+", " ", regex=True).str.strip())
                key_cat, key_name = part_key_cache[pkey]
                keep_mask = key_cat.isin(cats)
                for rule_cat_l, rule_strings in group_extra_rules.get(gk, []):
                    name_hit = pd.Series(False, index=part.index)
                    for rule_string in rule_strings:
                        name_hit = name_hit | key_name.str.contains(re.escape(rule_string), case=extra_include_match_case, na=False)
                    keep_mask = keep_mask | ((key_cat == rule_cat_l) & name_hit)
                group_mask_cache[mask_key] = keep_mask
            sub_mask = group_mask_cache[mask_key]
        sub = part if sub_mask is None else part[sub_mask]
        sub_value = sub[derived_components].sum(axis=1, min_count=1) if derived_components else sub[raw_col]
        id_key = (fkey, coll, id_col)
        if id_key not in id_str_cache:
            id_str_all = part[id_col].astype(str)
            id_codes, id_uniques = pd.factorize(id_str_all)
            id_printed_list = [name_map.get(re.sub(r"\s+", " ", s).strip().lower(), s) for s in id_uniques]
            id_key_list = [re.sub(r"\s+", " ", p).strip().lower() for p in id_printed_list]
            id_str_cache[id_key] = id_str_all
            id_printed_cache[id_key] = dict(zip(id_uniques, id_printed_list))
            printed_row_cache[id_key] = (pd.Series(np.array(id_printed_list, dtype=object)[id_codes], index=part.index), pd.Series(np.array(id_key_list, dtype=object)[id_codes], index=part.index))
        id_series = id_str_cache[id_key] if sub_mask is None else id_str_cache[id_key][sub_mask]
        uniq_ids = pd.unique(id_series)
        if printed_summary is not None:
            summary_key = re.sub(r"\s+", " ", printed_summary).strip().lower()
            key_series = pd.Series(summary_key, index=sub.index)
            dedupe = pd.DataFrame({"k": summary_key, "n": printed_summary, "i": uniq_ids})
            hint_src = printed_summary
        else:
            printed_all, key_all = printed_row_cache[id_key]
            key_series = key_all if sub_mask is None else key_all[sub_mask]
            uniq_printed = [id_printed_cache[id_key][s] for s in uniq_ids]
            dedupe = pd.DataFrame({"k": [re.sub(r"\s+", " ", p).strip().lower() for p in uniq_printed], "n": uniq_printed, "i": uniq_ids})
            hint_src = header
        hm = re.search(r"\(([^()]*)\)\s*$", hint_src.strip())
        target = unit_bp if unit_bp != "" else (hm.group(1).strip() if hm else raw_unit)
        t_l, f_l, thousand = target.lower().strip(), raw_unit, 1.0
        if t_l.startswith("1000·"):
            t_l, thousand = t_l[len("1000·"):], 1.0 / 1000.0
        t_l = "hours" if t_l == "h" else t_l
        if t_l == f_l:
            factor = 1.0 * thousand
        elif (f_l, t_l) in unit_rules:
            factor = unit_rules[(f_l, t_l)] * thousand
        else:
            factor = None
        if factor is None:
            cov["Status"], cov["Note"] = "NO UNIT RULE", f"UnitConversion has no rule {raw_unit} -> {target}"
            coverage_rows.append(cov)
            continue
        sub_value = sub_value * factor * sign
        if section_special_factor.get(tkey):
            cf_key = (fkey, coll)
            if cf_key not in child_factor_cache:
                child_codes, child_uniques = pd.factorize(part["Child Name"].astype(str))
                child_factors = np.array([contract_factor.get(re.sub(r"\s+", " ", s).strip().lower(), 1.0) for s in child_uniques], dtype=float)
                child_factor_cache[cf_key] = pd.Series(child_factors[child_codes] if len(child_factors) else np.array([], dtype=float), index=part.index)
            cf_all = child_factor_cache[cf_key]
            sub_value = sub_value * (cf_all if sub_mask is None else cf_all[sub_mask])
        work = pd.DataFrame({"Report Key": key_series, "Month Label": sub["Month Label"], "Value": sub_value})
        pv_grouped = work.groupby(["Report Key", "Month Label"])["Value"]
        pv = (pv_grouped.mean() if use_mean else pv_grouped.sum(min_count=1)).dropna().unstack("Month Label")
        pv = pv.reindex(columns=month_labels)
        disp = dedupe.drop_duplicates("k").set_index("k")["n"].to_dict()
        names = dedupe.groupby("k")["i"].agg(lambda s: " + ".join(sorted(set(str(x) for x in s)))).to_dict()
        ids = set(str(x) for x in sub[id_col]) if printed_summary is None else {generated}
        if tkey in extracted:
            extracted[tkey] = extracted[tkey].add(pv, fill_value=0.0)
            extracted_display[tkey].update({k: v for k, v in disp.items() if k not in extracted_display[tkey]})
            for k, v in names.items():
                extracted_names[tkey][k] = (extracted_names[tkey][k] + " + " + v) if k in extracted_names[tkey] else v
            extracted_raw_ids[tkey] |= ids
        else:
            extracted[tkey] = pv
            extracted_display[tkey] = dict(disp)
            extracted_names[tkey] = names
            extracted_raw_ids[tkey] = set(ids)
            extracted_idonly[tkey] = set()
            extracted_rate[tkey] = use_mean
        if derived_components:
            extracted_derived_keys.setdefault(tkey, set()).update(pv.index)
        cov["Status"] = "EXTRACTED" if not derived_components else "EXTRACTED (derived measure)"
        coverage_rows.append(cov)
    table_order.sort(key=section_sort_key)
    scope_missing_from_blueprint = [t for t in in_scope_tables if t not in table_order]
    cov_df = pd.DataFrame(coverage_rows)
    print(f"  Scope: {len(in_scope_tables)} Standard sections in scope; {len(out_of_scope_tables)} Blueprint_std sections outside the scope were excluded")
    if scope_missing_from_blueprint:
        print(f"  WARNING: in-scope section(s) not found in Blueprint_std: {scope_missing_from_blueprint}")
    if len(cov_df) > 0:
        print(f"  Blueprint_std: {len(cov_df)} rows; raw measure found for {int(cov_df['Status'].str.startswith('EXTRACTED').sum())} rows, raw column missing for {int((cov_df['Status'] == 'NO COUNTERPART - raw column not in the workbook').sum())} rows")
    return extracted, extracted_display, extracted_names, extracted_raw_ids, extracted_idonly, extracted_rate, extracted_derived_keys, cov_df, table_order, out_of_scope_tables, blueprint_titles
def build_structural_blank_report(structural_frames, rules, carrying_regions):
    """Structurally blank raw fields (Step 3 support): fields that can never carry a value (for example Offtake / Cost on the Generator collection, Peak Load of a region other than the carrying regions) are NOT applicable and are excluded from the expected count. One line per rule column: rows covered, blank fields (excluded), fields that unexpectedly hold a value and the applicable fields kept. Reads the raw frames it is given (Timeslice == All Periods only when they come from load_raw_frames_cached)."""
    rows_report = []
    carrying_keys = [re.sub(r"\s+", " ", r).strip().lower() for r in carrying_regions]
    for sheet_sb, collection_sb, columns_sb, carrying_rule, explanation_sb in rules:
        frame_sb = structural_frames[sheet_sb]
        sub_sb = frame_sb[frame_sb["Collection"] == collection_sb]
        for column_sb in columns_sb:
            if column_sb not in sub_sb.columns:
                rows_report.append({"Raw Sheet": sheet_sb, "Collection": collection_sb, "Column": column_sb, "Rule": explanation_sb, "Rows Covered": 0, "Structurally Blank Fields (excluded)": 0,
                                    "Unexpectedly Populated Fields": 0, "Applicable Fields (kept)": 0, "Note": "column is not present in the raw sheet"})
                continue
            if carrying_rule is not None:
                carries = sub_sb["Child Name"].astype(str).str.replace(r"\s+", " ", regex=True).str.strip().str.lower().isin(carrying_keys)
                blank_scope, applicable_scope = sub_sb[~carries], sub_sb[carries]
            else:
                blank_scope, applicable_scope = sub_sb, sub_sb.iloc[0:0]
            rows_report.append({"Raw Sheet": sheet_sb, "Collection": collection_sb, "Column": column_sb, "Rule": explanation_sb, "Rows Covered": int(len(blank_scope)),
                                "Structurally Blank Fields (excluded)": int(blank_scope[column_sb].isna().sum()), "Unexpectedly Populated Fields": int(blank_scope[column_sb].notna().sum()),
                                "Applicable Fields (kept)": int(len(applicable_scope)), "Note": ""})
    return pd.DataFrame(rows_report, columns=["Raw Sheet", "Collection", "Column", "Rule", "Rows Covered", "Structurally Blank Fields (excluded)", "Unexpectedly Populated Fields", "Applicable Fields (kept)", "Note"])
def build_population_jobs(reports, table_order, value_columns):
    """The sections the population engine processes: every section of both reports (Standard in section-number order, Ratings by key) plus two synthetic EMPTY sections ('Self-Test') that prove the engine itself copes with empty source data."""
    jobs = []
    for report_name in ["Standard Report", "Ratings Report"]:
        raw_tables_p, px_tables_p = reports[report_name]["Raw_tables"], reports[report_name]["PLEXOS_tables"]
        for table_number in get_ordered_section_keys(report_name, raw_tables_p, px_tables_p, table_order):
            jobs.append({"Report": report_name, "Table Number": table_number, "raw": raw_tables_p.get(table_number), "px": px_tables_p.get(table_number)})
    empty_frame_template = pd.DataFrame(columns=[""] + value_columns)
    jobs.append({"Report": "Self-Test", "Table Number": "empty-both", "raw": {"title": "(self-test) empty raw and empty output", "data": empty_frame_template.copy()},
                 "px": {"title": "(self-test) empty raw and empty output", "data": empty_frame_template.copy()}})
    jobs.append({"Report": "Self-Test", "Table Number": "empty-raw-zero-output", "raw": {"title": "(self-test) empty raw, zero-filled output", "data": empty_frame_template.copy()},
                 "px": {"title": "(self-test) empty raw, zero-filled output", "data": pd.DataFrame([["Unit A"] + ["0"] * len(value_columns)], columns=[""] + value_columns)}})
    return jobs
def read_output_fields(px_df, value_columns, null_tokens, idonly_keys):
    """The value fields of an OUTPUT section, all examined in one pass: row keys (normalized titles), populated-field matrix (a field is NULL when its stripped lower-case text is one of null_tokens), numeric matrix (NaN = not a number) and the applicable-row mask (structurally blank identifier-only rows are not applicable)."""
    px_keys = (px_df.iloc[:, 0].fillna("").astype(str) if px_df.shape[1] > 0 else pd.Series([], dtype=str)).str.replace(r"\s+", " ", regex=True).str.strip().str.lower().tolist()
    px_text = px_df.reindex(columns=value_columns).fillna("").astype(str)
    px_shape = (len(px_df), len(value_columns))
    if px_shape[0] > 0 and px_shape[1] > 0:
        px_nonnull = (~pd.Series(px_text.to_numpy().ravel()).str.strip().str.lower().isin(null_tokens)).to_numpy().reshape(px_shape)
        px_numeric = text_to_numeric_matrix(px_text)
    else:
        px_nonnull, px_numeric = np.zeros(px_shape, dtype=bool), np.zeros(px_shape, dtype=float)
    return px_keys, px_nonnull, px_numeric, ~np.array([k in idonly_keys for k in px_keys], dtype=bool)
def read_raw_fields(raw_df, value_columns, idonly_keys):
    """The value fields of a RAW section: row keys (normalized titles), populated-field matrix (a field is populated when it is a number) and the applicable-row mask (structurally blank identifier-only rows are not applicable)."""
    raw_keys = (raw_df.iloc[:, 0].fillna("").astype(str) if raw_df.shape[1] > 0 else pd.Series([], dtype=str)).str.replace(r"\s+", " ", regex=True).str.strip().str.lower().tolist()
    raw_nonnull = raw_df.reindex(columns=value_columns).apply(pd.to_numeric, errors="coerce").notna().to_numpy(dtype=bool)
    return raw_keys, raw_nonnull, ~np.array([k in idonly_keys for k in raw_keys], dtype=bool)
def find_matched_row_pairs(raw_keys, raw_applicable, px_keys, px_applicable):
    """Row positions by title key (applicable, titled rows only) and the matched pairs: same normalized title, occurrence by occurrence. Returns raw_pos, px_pos, pair_keys, pair_occurrences, pair_raw_rows, pair_px_rows."""
    raw_pos, px_pos = {}, {}
    for position, key in enumerate(raw_keys):
        if key != "" and bool(raw_applicable[position]):
            raw_pos.setdefault(key, []).append(position)
    for position, key in enumerate(px_keys):
        if key != "" and bool(px_applicable[position]):
            px_pos.setdefault(key, []).append(position)
    pair_keys, pair_occurrences, pair_raw_rows, pair_px_rows = [], [], [], []
    for key in sorted(set(raw_pos) & set(px_pos)):
        for occurrence in range(min(len(raw_pos[key]), len(px_pos[key]))):
            pair_keys.append(key)
            pair_occurrences.append(occurrence)
            pair_raw_rows.append(raw_pos[key][occurrence])
            pair_px_rows.append(px_pos[key][occurrence])
    return raw_pos, px_pos, pair_keys, pair_occurrences, pair_raw_rows, pair_px_rows
def find_unexpected_nulls(pair_keys, pair_occurrences, pair_raw_rows, pair_px_rows, raw_nonnull, px_nonnull, value_columns, report_name, table_number, table_title, raw_name_lookup):
    """Step 4: every matched row pair is compared in ONE array operation: a field populated in the raw data AND NULL in the output is an unexpected NULL. Returns null_fields_total, null_rows_total and one record per row with unexpected NULLs (the first 12 NULL columns are listed)."""
    null_fields_total, null_rows_total, null_records = 0, 0, []
    if len(pair_keys) > 0:
        pair_null_matrix = raw_nonnull[pair_raw_rows] & ~px_nonnull[pair_px_rows]
        pair_null_counts = pair_null_matrix.sum(axis=1)
        null_fields_total, null_rows_total = int(pair_null_counts.sum()), int((pair_null_counts > 0).sum())
        for pair_index in np.flatnonzero(pair_null_counts > 0).tolist():
            key, null_mask = pair_keys[pair_index], pair_null_matrix[pair_index]
            null_columns = [value_columns[i] for i in np.where(null_mask)[0]]
            null_records.append({"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Row Title": key, "Raw Data Name(s)": raw_name_lookup.get(key, ""), "Occurrence": pair_occurrences[pair_index] + 1,
                                 "Raw Populated Fields On The Row": int(raw_nonnull[pair_raw_rows[pair_index]].sum()), "Unexpected NULL Fields": int(null_mask.sum()),
                                 "NULL Columns": ", ".join(null_columns[:12]) + (f" (+{len(null_columns) - 12} more)" if len(null_columns) > 12 else "")})
    return null_fields_total, null_rows_total, null_records
def count_unpaired_rows(raw_pos, px_pos):
    """Rows that cannot be paired: raw rows with no output row (a row-presence finding for PlexOS-3.03B) and output rows with no raw row, counting surplus occurrences of a repeated title. Returns raw_rows_missing_from_output, output_rows_not_in_raw."""
    missing = int(sum(len(v) for k, v in raw_pos.items() if k not in px_pos) + sum(max(len(raw_pos[k]) - len(px_pos.get(k, [])), 0) for k in raw_pos if k in px_pos))
    extra = int(sum(len(v) for k, v in px_pos.items() if k not in raw_pos) + sum(max(len(px_pos[k]) - len(raw_pos.get(k, [])), 0) for k in px_pos if k in raw_pos))
    return missing, extra
def build_population_entry(job, value_columns, null_tokens, raw_standard_idonly, extracted_names, blueprint_titles, blank_title_rows_with_data, approved_nonnull_difference_pct, no_counterpart, ratings_no_raw_reason):
    """The population result of ONE section: populated value fields and data rows of the raw side (applicable rows only) and the output side, the non-null field-count difference (Step 3, 0% unless approved), the unexpected NULL fields of matched rows (Step 4), the empty-section checks (Step 5) and the section status. Any processing exception is recorded as a FAIL on the section instead of stopping the run. Returns entry, null_records (unexpected-NULL rows) and exception_record (None when nothing failed)."""
    report_name, table_number, raw_entry, px_entry = job["Report"], job["Table Number"], job["raw"], job["px"]
    raw_present, px_present = raw_entry is not None, px_entry is not None
    table_title = raw_entry["title"] if raw_present else (px_entry["title"] if px_present else blueprint_titles.get(table_number, ""))
    raw_name_lookup = extracted_names.get(table_number, {}) if report_name == "Standard Report" else {}
    entry = {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Present": raw_present, "PLEXOS Present": px_present, "Raw Data Rows": 0, "PLEXOS Data Rows": 0, "Raw Populated Fields": 0,
             "PLEXOS Populated Fields": 0, "Non-Null Field Difference": 0, "Non-Null Field Difference %": np.nan, "Approved Difference": False, "Unexpected NULL Fields": 0, "Unexpected NULL Rows": 0, "Blank Row Titles With Data": 0,
             "Missing Value Columns": 0, "Raw Rows Missing From Output": 0, "Output Rows Not In Raw": 0, "Structurally Blank Rows Excluded (Raw)": 0, "Structurally Blank Rows Excluded (Output)": 0, "Output Non-Numeric Fields": 0,
             "Has Data Row (Step 2)": "", "Non-Null Count Matches (Step 3)": "", "No Unexpected NULLs (Step 4)": "", "Empty Source Valid (Step 5)": "", "Raw Section Empty": "", "Section Status": "", "Note": ""}
    null_records, exception_record = [], None
    try:
        idonly_keys = raw_standard_idonly.get(table_number, set()) if report_name == "Standard Report" else set()
        if px_present:
            px_df = px_entry["data"]
            px_keys, px_nonnull, px_numeric, px_applicable = read_output_fields(px_df, value_columns, null_tokens, idonly_keys)
            entry["PLEXOS Populated Fields"] = int(px_nonnull[px_applicable].sum())
            entry["PLEXOS Data Rows"] = int(px_nonnull[px_applicable].any(axis=1).sum()) if px_nonnull.shape[0] > 0 else 0
            entry["Structurally Blank Rows Excluded (Output)"] = int((~px_applicable).sum())
            entry["Output Non-Numeric Fields"] = int((px_nonnull & np.isnan(px_numeric))[px_applicable].sum())
            entry["Missing Value Columns"] = len([c for c in value_columns if c not in px_df.columns])
            entry["Blank Row Titles With Data"] = len([b for b in blank_title_rows_with_data if b["Report"] == report_name and b["Table Number"] == table_number])
        if raw_present:
            raw_keys, raw_nonnull, raw_applicable = read_raw_fields(raw_entry["data"], value_columns, idonly_keys)
            entry["Raw Populated Fields"] = int(raw_nonnull[raw_applicable].sum())
            entry["Raw Data Rows"] = int(raw_nonnull[raw_applicable].any(axis=1).sum()) if raw_nonnull.shape[0] > 0 else 0
            entry["Structurally Blank Rows Excluded (Raw)"] = int((~raw_applicable).sum())
        if not raw_present:
            entry["Section Status"] = "N/A - " + no_counterpart
            entry["Non-Null Field Difference"] = np.nan
            entry["Note"] = ratings_no_raw_reason if report_name == "Ratings Report" else "Section has no raw counterpart (no raw measure for it in the raw data)"
        elif not px_present:
            entry["Section Status"] = "FAIL"
            entry["Has Data Row (Step 2)"] = False if entry["Raw Data Rows"] > 0 else "N/A"
            entry["Non-Null Field Difference"] = -entry["Raw Populated Fields"]
            entry["Non-Null Field Difference %"] = -100.0 if entry["Raw Populated Fields"] > 0 else 0.0
            entry["Non-Null Count Matches (Step 3)"] = entry["Raw Populated Fields"] == 0
            entry["Note"] = "mapped section is missing from the PLEXOS output"
        else:
            raw_has_data = entry["Raw Data Rows"] > 0
            entry["Raw Section Empty"] = not raw_has_data
            entry["Has Data Row (Step 2)"] = (entry["PLEXOS Data Rows"] >= 1) if raw_has_data else "N/A"
            difference = entry["PLEXOS Populated Fields"] - entry["Raw Populated Fields"]
            entry["Non-Null Field Difference"] = difference
            if entry["Raw Populated Fields"] > 0:
                entry["Non-Null Field Difference %"] = 100.0 * difference / entry["Raw Populated Fields"]
            else:
                entry["Non-Null Field Difference %"] = 0.0 if difference == 0 else np.inf
            allowed_pct = approved_nonnull_difference_pct.get(table_number) if report_name == "Standard Report" else None
            count_ok = (difference == 0)
            if (not count_ok) and allowed_pct is not None and np.isfinite(entry["Non-Null Field Difference %"]) and abs(entry["Non-Null Field Difference %"]) <= allowed_pct:
                count_ok = True
                entry["Approved Difference"] = True
            entry["Non-Null Count Matches (Step 3)"] = count_ok
            raw_pos, px_pos, pair_keys, pair_occurrences, pair_raw_rows, pair_px_rows = find_matched_row_pairs(raw_keys, raw_applicable, px_keys, px_applicable)
            null_fields_total, null_rows_total, null_records = find_unexpected_nulls(pair_keys, pair_occurrences, pair_raw_rows, pair_px_rows, raw_nonnull, px_nonnull, value_columns, report_name, table_number, table_title, raw_name_lookup)
            entry["Unexpected NULL Fields"], entry["Unexpected NULL Rows"] = null_fields_total, null_rows_total
            entry["Raw Rows Missing From Output"], entry["Output Rows Not In Raw"] = count_unpaired_rows(raw_pos, px_pos)
            entry["Output Rows Not In Raw"] += entry["Blank Row Titles With Data"]
            entry["No Unexpected NULLs (Step 4)"] = bool(null_fields_total == 0 and entry["Blank Row Titles With Data"] == 0 and entry["Missing Value Columns"] == 0)
            fabricated = bool(np.nansum(np.abs(px_numeric[px_applicable])) > 0) if px_numeric.shape[0] > 0 else False
            header_valid = entry["Missing Value Columns"] == 0
            entry["Empty Source Valid (Step 5)"] = (header_valid and not fabricated) if not raw_has_data else "N/A"
            problems = []
            if raw_has_data and entry["PLEXOS Data Rows"] < 1:
                problems.append("raw section has data but the output section has no data row")
            if not count_ok:
                problems.append(f"non-null fields differ ({entry['PLEXOS Populated Fields']} output vs {entry['Raw Populated Fields']} raw)")
            if null_fields_total > 0:
                problems.append(f"{null_fields_total} field(s) NULL in the output where the raw data has a value")
            if entry["Blank Row Titles With Data"] > 0:
                problems.append(f"{entry['Blank Row Titles With Data']} output data row(s) with a NULL row title")
            if entry["Missing Value Columns"] > 0:
                problems.append(f"{entry['Missing Value Columns']} value column(s) missing from the output")
            if not raw_has_data and not (header_valid and not fabricated):
                problems.append("empty raw section: output is not a valid section")
            entry["Section Status"] = "PASS" if len(problems) == 0 else "FAIL"
            entry["Note"] = "; ".join(problems)
    except Exception as exc:
        exception_record = {"Report": report_name, "Table Number": table_number, "Error": f"{type(exc).__name__}: {exc}"}
        entry["Section Status"] = "FAIL"
        entry["Note"] = f"processing exception: {type(exc).__name__}: {exc}"
    return entry, null_records, exception_record
def split_population_results(all_population):
    """Split the population table: the engine self-test lines, the real sections, the mapped sections (a raw counterpart exists), the compared sections (present on both sides) and the sections listed as having no counterpart. Raw Present / PLEXOS Present are forced to real booleans first so '~' can never turn True / False into -2 / -1."""
    all_population["Raw Present"] = all_population["Raw Present"].astype(bool)
    all_population["PLEXOS Present"] = all_population["PLEXOS Present"].astype(bool)
    selftest_results = all_population[all_population["Report"] == "Self-Test"].copy()
    population_results = all_population[all_population["Report"] != "Self-Test"].copy().reset_index(drop=True)
    mapped_pop = population_results[population_results["Raw Present"]]
    compared_pop = population_results[population_results["Raw Present"] & population_results["PLEXOS Present"]]
    unmapped_pop = population_results[population_results["Section Status"].astype(str).str.startswith("N/A")]
    return selftest_results, population_results, mapped_pop, compared_pop, unmapped_pop
def check_empty_source_report(report_label, report_path, reference_keys, value_columns, null_tokens, ratings_key_aliases):
    """Step 5a: a report generated from an EMPTY source dataset must contain every section of the real run with the full month / Tot-YYYY / Total header, only blank or zero values (nothing fabricated), no non-numeric garbage and no error text. Returns one result row per section check (Status PASS / FAIL with a note)."""
    empty_run_rows = []
    try:
        with open(report_path, "r", encoding="utf-8-sig", errors="replace") as file:
            rows_e = list(csv.reader(file))
    except Exception as exc:
        return [{"Report": report_label, "Table Number": "(file)", "Section Present": False, "Header Valid": False, "Values Valid": False, "Status": "FAIL", "Note": f"the empty-source report could not be read: {type(exc).__name__}: {exc}"}]
    sections_e, current_key_e = {}, None
    file_text_lower = " ".join(" ".join(r) for r in rows_e).lower()
    for row in rows_e:
        non_blank_e = [str(cell).strip() for cell in row if str(cell).strip()]
        row_text_e = " ".join(non_blank_e)
        is_header_e = bool(re.match(r"^\(\s*\d+[a-zA-Z]?\s*\)", row_text_e)) if report_label == "Standard Report" else (len(non_blank_e) == 1)
        if is_header_e:
            if report_label == "Standard Report":
                current_key_e = re.match(r"^\(\s*(\d+[a-zA-Z]?)\s*\)", row_text_e).group(1).lower()
            else:
                key_text = re.sub(r"\([^)]*\)", "", row_text_e.lower().strip())
                day_token_e = r"(?:mon|tue|tues|wed|weds|thu|thur|thurs|fri|sat|sun|sunday|monday|tuesday|wednesday|thursday|friday|saturday)"
                key_text = re.sub(rf"\b{day_token_e}\s*-\s*{day_token_e}\b", "", key_text)
                current_key_e = ratings_key_aliases.get(re.sub(r"[^a-z0-9]+", "", key_text), re.sub(r"[^a-z0-9]+", "", key_text))
            sections_e.setdefault(current_key_e, [])
        elif current_key_e is not None and len(non_blank_e) > 0:
            sections_e[current_key_e].append([str(c).strip() for c in row])
    for key_e in reference_keys:
        if key_e not in sections_e:
            empty_run_rows.append({"Report": report_label, "Table Number": key_e, "Section Present": False, "Header Valid": False, "Values Valid": False, "Status": "FAIL", "Note": "section is missing from the report generated from the empty source"})
            continue
        section_rows_e = sections_e[key_e]
        header_e = section_rows_e[0] if len(section_rows_e) > 0 else []
        header_valid_e = len(header_e) > 1 and header_e[1:1 + len(value_columns)] == value_columns and len(header_e[1:]) >= len(value_columns)
        candidate_cells_e = []
        for data_row_e in section_rows_e[1:]:
            label_e = re.sub(r"\s+", " ", data_row_e[0]).strip().lower() if len(data_row_e) > 0 else ""
            if label_e in ("", "total") or label_e.startswith("("):
                continue
            candidate_cells_e.extend(cell_e.replace(",", "") for cell_e in data_row_e[1:] if cell_e.strip().lower() not in null_tokens)
        if len(candidate_cells_e) > 0:
            numeric_cells_e = pd.to_numeric(pd.Series(candidate_cells_e, dtype=object), errors="coerce").to_numpy(dtype=float)
            nan_cells_e = np.isnan(numeric_cells_e)
            non_numeric_e, fabricated_e = int(nan_cells_e.sum()), int((np.abs(numeric_cells_e[~nan_cells_e]) > 0).sum())
        else:
            non_numeric_e, fabricated_e = 0, 0
        values_valid_e = (fabricated_e == 0 and non_numeric_e == 0)
        notes_e = []
        if not header_valid_e:
            notes_e.append("header is not the full set of month / Tot-YYYY / Total columns")
        if fabricated_e > 0:
            notes_e.append(f"{fabricated_e} non-zero value(s) in a report generated from an empty source")
        if non_numeric_e > 0:
            notes_e.append(f"{non_numeric_e} non-numeric value(s)")
        empty_run_rows.append({"Report": report_label, "Table Number": key_e, "Section Present": True, "Header Valid": header_valid_e, "Values Valid": values_valid_e, "Status": "PASS" if (header_valid_e and values_valid_e) else "FAIL", "Note": "; ".join(notes_e)})
    if any(token in file_text_lower for token in ("traceback", "exception", "error")):
        empty_run_rows.append({"Report": report_label, "Table Number": "(file)", "Section Present": True, "Header Valid": True, "Values Valid": False, "Status": "FAIL", "Note": "the report generated from the empty source contains error / exception text"})
    return empty_run_rows
def evaluate_engine_selftest(selftest_results):
    """Step 5c: the engine self-test on synthetic empty sections: empty raw and empty output -> PASS with 0 populated fields and a 0% difference; empty raw and zero-filled output -> a valid empty section (the extra zero fields are reported as a count difference). No self-test line may be a processing exception."""
    selftest_both = selftest_results[selftest_results["Table Number"] == "empty-both"]
    selftest_zero = selftest_results[selftest_results["Table Number"] == "empty-raw-zero-output"]
    return bool((len(selftest_results) == 2) and (not selftest_results["Note"].astype(str).str.startswith("processing exception").any()) and (len(selftest_both) == 1) and (selftest_both["Section Status"] == "PASS").all()
                and (selftest_both["Raw Populated Fields"] == 0).all() and (selftest_both["PLEXOS Populated Fields"] == 0).all() and (selftest_both["Non-Null Field Difference %"] == 0).all()
                and (len(selftest_zero) == 1) and (selftest_zero["Empty Source Valid (Step 5)"] == True).all() and (selftest_zero["Raw Data Rows"] == 0).all())
def verify_population_files(summary_path, exceptions_path, structural_blank_path, n_summary_rows, n_exception_rows):
    """Step 6: the population summary is read back and checked (file exists, one row per section, the required columns, both datasets recorded, no Self-Test line); the unexpected-NULL report is read back (row count) and the structurally blank fields report must exist. Returns {check label: bool}."""
    labels = (f"Every section recorded ({n_summary_rows} rows)", "Report type, section, row count, populated field count, difference and unexpected NULL columns present", "Results recorded for both datasets (Standard and Ratings)", "Self-test sections kept out of the summary")
    checks = {"Population summary written (file exists)": summary_path.is_file()}
    if summary_path.is_file():
        readback_summary = pd.read_csv(summary_path)
        required_summary_columns = ["Report", "Table Number", "Raw Data Rows", "PLEXOS Data Rows", "Raw Populated Fields", "PLEXOS Populated Fields", "Non-Null Field Difference", "Unexpected NULL Fields", "Section Status"]
        checks[labels[0]] = len(readback_summary) == n_summary_rows
        checks[labels[1]] = all(c in readback_summary.columns for c in required_summary_columns)
        checks[labels[2]] = set(readback_summary["Report"]) == {"Standard Report", "Ratings Report"}
        checks[labels[3]] = bool((readback_summary["Report"] != "Self-Test").all())
    else:
        for label in labels:
            checks[label] = False
    try:
        exceptions_rows_ok = len(pd.read_csv(exceptions_path)) == n_exception_rows
    except pd.errors.EmptyDataError:
        exceptions_rows_ok = n_exception_rows == 0
    checks[f"Unexpected-NULL report written and read back ({n_exception_rows} row(s))"] = exceptions_path.is_file() and exceptions_rows_ok
    checks["Structurally blank fields report written"] = structural_blank_path.is_file()
    return checks

################################################################################################################################################################################
#3.05
################################################################################################################################################################################
def load_generator_name_map(template_xl, map_sheet):
    """Generator_name_map: the printed-name / Resources_Plexos pairs of the template's maptable sheet (the Resources_Plexos column is the raw name, the first other column the name printed in the reports it is replaced by; names stripped, 'nan' = blank, fully blank rows ignored, 'Map Row' = the spreadsheet row, header = row 1). The pairs are returned with the columns Resources_Output / Resources_Plexos / Map Row. Prints one line. Returns gen_map, gen_map_error ('' when fine). REPLACES the existing function."""
    gen_map_error, gen_map_blank_rows = "", 0
    gen_map = pd.DataFrame(columns=["Resources_Output", "Resources_Plexos", "Map Row"])
    try:
        map_sheets_present = [sn for sn in template_xl.sheet_names if sn.lower().startswith("maptable")]
        gen_map_sheet_found = [sn for sn in map_sheets_present if sn.strip().lower() == map_sheet.lower()]
        if len(gen_map_sheet_found) == 0:
            raise KeyError(f"worksheet '{map_sheet}' not found (maptable_ sheets present: {map_sheets_present})")
        gen_map_raw = template_xl.parse(gen_map_sheet_found[0], header=0, dtype=str).copy()
        gen_map_raw.columns = [str(col).strip() for col in gen_map_raw.columns]
        columns_lower = [str(col).lower() for col in gen_map_raw.columns]
        if gen_map_raw.shape[1] < 2 or "resources_plexos" not in columns_lower:
            gen_map_error = f"sheet '{map_sheet}' must have a Resources_Plexos column and the printed-name column (found: {list(gen_map_raw.columns)})"
        else:
            plexos_position = columns_lower.index("resources_plexos")
            gen_map_raw = gen_map_raw.iloc[:, [[i for i in range(gen_map_raw.shape[1]) if i != plexos_position][0], plexos_position]].copy()
            gen_map_raw.columns = ["Resources_Output", "Resources_Plexos"]
            for map_column in ["Resources_Output", "Resources_Plexos"]:
                gen_map_raw[map_column] = gen_map_raw[map_column].fillna("").astype(str).str.strip()
                gen_map_raw.loc[gen_map_raw[map_column].str.lower() == "nan", map_column] = ""
            fully_blank = (gen_map_raw["Resources_Output"] == "") & (gen_map_raw["Resources_Plexos"] == "")
            gen_map_blank_rows = int(fully_blank.sum())
            gen_map = gen_map_raw[~fully_blank].reset_index(drop=True)
            gen_map["Map Row"] = gen_map_raw.index[~fully_blank] + 2
    except Exception as exc:
        gen_map_error = f"sheet '{map_sheet}' could not be read from the template workbook: {type(exc).__name__}: {exc}"
    print(f"Generator_name_map ({map_sheet}): {len(gen_map)} pair row(s) to evaluate; {gen_map_blank_rows} fully blank row(s) ignored{'; ERROR: ' + gen_map_error if gen_map_error else ''}")
    return gen_map, gen_map_error
def build_raw_name_locations(raw_frames):
    """Where every name exists in the raw workbook itself, whatever report section it feeds: casefold_name -> set of location texts. Generator tab: Child Name of the Generator rows (with their Category), Parent Name and Child Name of the Generator.Fuels rows; Region tab and Battery tab: Child Name. raw_frames = {'df_gen': ..., 'df_reg': ..., 'df_bat': ...} (the frames already limited to the All Periods rows)."""
    locations = {}
    for frame_key, sheet_label in (("df_gen", "Generator tab"), ("df_reg", "Region tab"), ("df_bat", "Battery tab")):
        frame = raw_frames.get(frame_key)
        if frame is None or "Collection" not in frame.columns or "Child Name" not in frame.columns:
            continue
        columns = [c for c in ("Collection", "Parent Name", "Child Name", "Category") if c in frame.columns]
        for record in frame[columns].drop_duplicates().to_dict("records"):
            collection = str(record.get("Collection", "")).strip()
            category = str(record.get("Category", "")).strip()
            category_text = f", category {category}" if category.lower() not in ("", "nan", "-") else ""
            child_key = casefold_name(record.get("Child Name", ""))
            if child_key not in ("", "nan"):
                locations.setdefault(child_key, set()).add(f"{sheet_label} Child Name ({collection}{category_text})")
            parent_key = casefold_name(record.get("Parent Name", ""))
            if collection == "Generator.Fuels" and parent_key not in ("", "nan"):
                locations.setdefault(parent_key, set()).add(f"{sheet_label} Parent Name ({collection})")
    return locations
def parse_written_sections(text):
    """Section keys at the start of a written section text (the inverse of join_sections). A text that starts with 'NOT FOUND', 'None' or 'N/A' means no section, and a note in brackets after the list is ignored ('21, 22 (raw data: ...)' -> 21, 22). Used instead of parse_section_list for the results columns written by build_mapping_results."""
    text = str(text).strip()
    if text.startswith(("NOT FOUND", "None", "N/A")):
        return set()
    return set(t.strip() for t in text.split(" (")[0].split(",") if t.strip())
def evaluate_name_map_pairs(gen_map, raw_exact_to_tables, raw_norm_to_tables, out_exact_to_tables, out_norm_to_tables, relevant_tables, raw_locations=None, both_exist_matches=True):
    """Pair engine: every Generator_name_map pair is evaluated against the same relevant sections. Resources_Plexos is looked up in the raw data and Resources_Output in the output (both case- and whitespace-tolerant). A resource EXISTS in the raw data when it feeds a raw section or is found in raw_locations (the raw workbook itself), and in the output when it is printed in any section. Tables_Match is True when neither name is blank and the two relevant-section sets are equal and not empty. When both sets are empty it is True only when both_exist_matches is True and both resources exist (they are then simply outside the relevant sections on both sides); a resource that exists on one side only, or on neither, stays a mismatch. The record keeps the full sets so the steps can re-verify them. REPLACES the existing function (two optional arguments added at the end)."""
    pair_records = []
    for map_row in gen_map.to_dict("records"):
        output_name, plexos_name = map_row["Resources_Output"], map_row["Resources_Plexos"]
        output_key, plexos_key = casefold_name(output_name), casefold_name(plexos_name)
        raw_all = set(raw_norm_to_tables.get(plexos_key, set())) if plexos_key != "" else set()
        out_all = set(out_norm_to_tables.get(output_key, set())) if output_key != "" else set()
        raw_where = set(raw_locations.get(plexos_key, set())) if (raw_locations is not None and plexos_key != "") else set()
        raw_exists, out_exists = bool(raw_all or raw_where), bool(out_all)
        raw_rel, out_rel = raw_all & relevant_tables, out_all & relevant_tables
        only_raw, only_out = raw_rel - out_rel, out_rel - raw_rel
        blank_side = (output_name == "") or (plexos_name == "")
        sets_equal = (not only_raw) and (not only_out)
        out_of_scope_match = bool((not blank_side) and sets_equal and (not raw_rel) and (not out_rel) and both_exist_matches and raw_exists and out_exists)
        tables_match = bool((not blank_side) and sets_equal and (len(raw_rel) > 0 or out_of_scope_match))
        pair_records.append({"Map Row": int(map_row["Map Row"]), "Resources_Output": output_name, "Resources_Plexos": plexos_name, "output_key": output_key, "plexos_key": plexos_key, "raw_all": raw_all, "out_all": out_all,
                             "raw_where": raw_where, "raw_exists": raw_exists, "out_exists": out_exists, "raw_rel": raw_rel, "out_rel": out_rel, "only_raw": only_raw, "only_out": only_out, "blank_side": blank_side,
                             "both_exist_matches": bool(both_exist_matches), "out_of_scope_match": out_of_scope_match, "tables_match": tables_match,
                             "exact_raw": set(raw_exact_to_tables.get(plexos_name, set())) if plexos_name != "" else set(), "exact_out": set(out_exact_to_tables.get(output_name, set())) if output_name != "" else set()})
    return pair_records
def build_mapping_results(pair_records, relevant_tables, relevant_rating_sections, ratings_have_raw, child_names_lower, child_names_error):
    """The full results table, one row per pair (matched or not): the relevant sections of each resource, Tables_Match, the sections only on one side, whether Resources_Plexos is in NewPlexosResourceNames (only for mismatches: Yes / No / Unavailable), the complete section membership of both resources (for mismatches and for pairs that match only because both resources are outside the relevant sections), the rating sections (informational) and the match detail. A resource that exists but is in no relevant section says so instead of 'NOT FOUND'; 'NOT FOUND' is written only for a resource that is not in the raw workbook / not printed in any report section. REPLACES the existing function: no column mentions the old pair-name wording (Resources_Output, Output_Relevant_Tables (Resources_Output in output), Resources_Output_All_Tables)."""
    results_rows = []
    for rec in pair_records:
        raw_where_text = "; ".join(sorted(rec["raw_where"]))
        if rec["raw_rel"]:
            raw_rel_text = join_sections(rec["raw_rel"])
        else:
            raw_rel_text = "None of the relevant sections (the resource is in the raw data)" if rec["raw_exists"] else "NOT FOUND in the raw data"
        if rec["out_rel"]:
            out_rel_text = join_sections(rec["out_rel"])
        else:
            out_rel_text = "None of the relevant sections (the resource is printed in other sections)" if rec["out_exists"] else "NOT FOUND in the output"
        show_all_tables = (not rec["tables_match"]) or rec["out_of_scope_match"]
        if not show_all_tables:
            in_new_names = raw_all_text = out_all_text = "N/A (Tables_Match is True)"
        else:
            if rec["tables_match"]:
                in_new_names = "N/A (Tables_Match is True)"
            elif rec["plexos_key"] == "":
                in_new_names = "No"
            elif child_names_error != "":
                in_new_names = "Unavailable"
            else:
                in_new_names = "Yes" if rec["plexos_key"] in child_names_lower else "No"
            if rec["raw_exists"]:
                raw_all_text = join_sections(rec["raw_all"], "None") + (f" (raw data: {raw_where_text})" if raw_where_text else "")
            else:
                raw_all_text = "NOT FOUND in any table or in the raw data"
            out_all_text = join_sections(rec["out_all"]) if rec["out_exists"] else "NOT FOUND in any table"
        pieces = []
        if rec["tables_match"]:
            detail = "Both resources appear in exactly the same relevant sections" if rec["raw_rel"] else f"Both resources exist (raw data and output) but neither is in a relevant section; the output prints the resource only in: {join_sections(rec['out_all'])}"
        else:
            if rec["blank_side"]:
                pieces.append("the pair has a blank Resources_Output or Resources_Plexos name")
            if rec["only_raw"]:
                pieces.append("only in the raw data: " + join_sections(rec["only_raw"]))
            if rec["only_out"]:
                pieces.append("only in the output: " + join_sections(rec["only_out"]))
            if (not rec["raw_rel"]) and (not rec["out_rel"]) and (not rec["blank_side"]):
                if not rec["raw_exists"]:
                    pieces.append("Resources_Plexos is not in the raw data")
                if not rec["out_exists"]:
                    pieces.append("Resources_Output is not printed in any report section")
                if rec["raw_exists"] and rec["out_exists"]:
                    pieces.append("both resources exist but neither appears in any relevant section")
            detail = "; ".join(pieces)
        informational_ratings = "compared (see the relevant-table columns)" if ratings_have_raw else join_sections(rec["out_all"] & set(relevant_rating_sections))
        results_rows.append({"Map Row": rec["Map Row"], "Resources_Output": rec["Resources_Output"] if rec["Resources_Output"] != "" else "(blank)", "Resources_Plexos": rec["Resources_Plexos"] if rec["Resources_Plexos"] != "" else "(blank)",
                             "Raw_Relevant_Tables (Resources_Plexos in solution.zip)": raw_rel_text, "Output_Relevant_Tables (Resources_Output in output)": out_rel_text, "Tables_Match": rec["tables_match"],
                             "Tables_Only_In_Raw": join_sections(rec["only_raw"]), "Tables_Only_In_Output": join_sections(rec["only_out"]), "Resources_Plexos_In_NewPlexosResourceNames": in_new_names,
                             "Resources_Plexos_Raw_All_Tables": raw_all_text, "Resources_Output_All_Tables": out_all_text, "Output_Rating_Sections (informational)": informational_ratings, "Match_Detail": detail})
    results_columns = ["Map Row", "Resources_Output", "Resources_Plexos", "Raw_Relevant_Tables (Resources_Plexos in solution.zip)", "Output_Relevant_Tables (Resources_Output in output)", "Tables_Match", "Tables_Only_In_Raw",
                       "Tables_Only_In_Output", "Resources_Plexos_In_NewPlexosResourceNames", "Resources_Plexos_Raw_All_Tables", "Resources_Output_All_Tables", "Output_Rating_Sections (informational)", "Match_Detail"]
    results_df = pd.DataFrame(results_rows, columns=results_columns)
    results_df["Tables_Match"] = results_df["Tables_Match"].astype(bool)
    return results_df
def check_relevant_section_scope(pair_records, relevant_tables):
    """Step 3: only the relevant sections may affect a match result: no section outside the relevant set in a relevant-sections column, and every match result equals the result recomputed from the full membership restricted to the relevant sections (and the existence of both resources when both sets are empty). Also counts the pairs that also appear outside the relevant scope and the pairs whose result would differ if those sections counted. Returns leaks, recompute_mismatches, scope_would_change, outside_relevant_pairs. REPLACES the existing function."""
    leaks, recompute_mismatches, scope_would_change = [], [], 0
    for rec in pair_records:
        for side_label, rel_set in (("raw", rec["raw_rel"]), ("output", rec["out_rel"])):
            outside = sorted([t for t in rel_set if t not in relevant_tables], key=mixed_section_sort_key)
            if len(outside) > 0:
                leaks.append((rec["Resources_Output"], rec["Resources_Plexos"], side_label, outside))
        independent_raw, independent_out = set(t for t in rec["raw_all"] if t in relevant_tables), set(t for t in rec["out_all"] if t in relevant_tables)
        independent_match = bool((not rec["blank_side"]) and independent_raw == independent_out and (len(independent_raw) > 0 or (rec["both_exist_matches"] and rec["raw_exists"] and rec["out_exists"])))
        if independent_match != rec["tables_match"]:
            recompute_mismatches.append((rec["Resources_Output"], rec["Resources_Plexos"]))
        if bool((not rec["blank_side"]) and rec["raw_all"] == rec["out_all"] and (len(rec["raw_all"]) > 0 or len(rec["out_all"]) > 0)) != rec["tables_match"]:
            scope_would_change += 1
    outside_relevant_pairs = sum(1 for rec in pair_records if len([t for t in rec["raw_all"] | rec["out_all"] if t not in relevant_tables]) > 0)
    return leaks, recompute_mismatches, scope_would_change, outside_relevant_pairs
def check_lookup_tolerance(pair_records, raw_norm_to_tables, out_norm_to_tables, raw_locations=None):
    """Step 4: every pair name is looked up again as a case-swapped, a double-spaced and an upper-case padded variant (raw side: Resources_Plexos, in the raw sections and, when raw_locations is given, in the raw workbook itself; output side: Resources_Output) and must resolve to the same sections / locations; the pairs that resolve only thanks to the tolerance (an exact-case lookup would have missed a section) are listed. Returns variants_tested, variant_failures, resolved_only_by_tolerance. REPLACES the existing function."""
    variant_failures, variants_tested, resolved_only_by_tolerance = [], 0, []
    for rec in pair_records:
        lookups = [("raw data", rec["Resources_Plexos"], raw_norm_to_tables, rec["raw_all"]), ("output", rec["Resources_Output"], out_norm_to_tables, rec["out_all"])]
        if raw_locations is not None:
            lookups.append(("raw data (names)", rec["Resources_Plexos"], raw_locations, rec["raw_where"]))
        for side_label, name_text, index_norm, baseline in lookups:
            if name_text == "":
                continue
            for variant_label, variant_text in (("case swapped", "  " + name_text.swapcase() + "  "), ("double spaced", name_text.replace(" ", "  ")), ("upper case, padded", "\t" + name_text.upper() + " ")):
                variants_tested += 1
                if set(index_norm.get(casefold_name(variant_text), set())) != baseline:
                    variant_failures.append((side_label, name_text, variant_label))
        if (rec["raw_all"] != rec["exact_raw"]) or (rec["out_all"] != rec["exact_out"]):
            resolved_only_by_tolerance.append((rec["Resources_Output"], rec["Resources_Plexos"]))
    return variants_tested, variant_failures, resolved_only_by_tolerance
def find_inconsistent_matches(results_df, both_exist_matches=True):
    """Step 5: the stored Tables_Match of every result row must equal the value recomputed from the WRITTEN relevant-section columns (equal sets, no blank name, and not empty; when both are empty the match needs both resources to exist, i.e. neither column says 'NOT FOUND', and both_exist_matches True). Returns the (Resources_Output, Resources_Plexos) of every row that disagrees. REPLACES the existing function."""
    inconsistent = []
    raw_column, out_column = "Raw_Relevant_Tables (Resources_Plexos in solution.zip)", "Output_Relevant_Tables (Resources_Output in output)"
    for result_row in results_df.to_dict("records"):
        raw_parsed, out_parsed = parse_written_sections(result_row[raw_column]), parse_written_sections(result_row[out_column])
        both_exist = (not str(result_row[raw_column]).startswith("NOT FOUND")) and (not str(result_row[out_column]).startswith("NOT FOUND"))
        blank_pair = (result_row["Resources_Output"] in ("", "(blank)")) or (result_row["Resources_Plexos"] in ("", "(blank)"))
        if bool((not blank_pair) and raw_parsed == out_parsed and (len(raw_parsed) > 0 or (both_exist_matches and both_exist))) != bool(result_row["Tables_Match"]):
            inconsistent.append((result_row["Resources_Output"], result_row["Resources_Plexos"]))
    return inconsistent
def check_complete_membership(pair_records, results_df, relevant_tables):
    """Step 7: for every mismatched pair the complete section membership of both resources (not limited to the relevant subset) is captured and equals the lookup result, the relevant sections are a subset of it and no value is blank. Returns blank_values, subset_violations, outside_scope_captured. REPLACES the existing function."""
    blank_values = subset_violations = outside_scope_captured = 0
    for rec, result_row in zip(pair_records, results_df.to_dict("records")):
        if rec["tables_match"]:
            continue
        raw_text, out_text = result_row["Resources_Plexos_Raw_All_Tables"], result_row["Resources_Output_All_Tables"]
        if str(raw_text).strip() == "" or str(out_text).strip() == "":
            blank_values += 1
        raw_listed, out_listed = parse_written_sections(raw_text), parse_written_sections(out_text)
        if (raw_listed != rec["raw_all"]) or (out_listed != rec["out_all"]) or (not rec["raw_rel"] <= raw_listed) or (not rec["out_rel"] <= out_listed):
            subset_violations += 1
        outside_scope_captured += len([t for t in (raw_listed | out_listed) if t not in relevant_tables])
    return blank_values, subset_violations, outside_scope_captured
def write_and_verify_mapping_results(results_df, mismatches, gen_map, results_folder):
    """Step 8: write the full results file (one row per pair, matched or not) and the mismatch file, read the results back and check: file written, one row per Generator_name_map pair, the membership / diagnostic columns present, every diagnostic column populated (no null / blank value), matched and mismatched pairs both present, mismatch file written. Returns results_output_path, exceptions_output_path, step8_checks. REPLACES the existing function (new column names)."""
    results_output_path = save_results_csv(results_df, results_folder, "PlexOS_3_05_Resource_Mapping_Results.csv")
    exceptions_output_path = save_results_csv(mismatches, results_folder, "PlexOS_3_05_Resource_Mapping_Mismatches.csv")
    step8_checks = {"Results file written": results_output_path.is_file()}
    label_one_row = f"One row per Generator_name_map pair ({{}} row(s) written, {len(gen_map)} pair(s) in the map)"
    if results_output_path.is_file():
        readback = pd.read_csv(results_output_path, dtype=str, keep_default_na=False)
        required_result_columns = ["Resources_Output", "Resources_Plexos", "Raw_Relevant_Tables (Resources_Plexos in solution.zip)", "Output_Relevant_Tables (Resources_Output in output)", "Tables_Match",
                                   "Resources_Plexos_In_NewPlexosResourceNames", "Resources_Plexos_Raw_All_Tables", "Resources_Output_All_Tables"]
        step8_checks[label_one_row.format(len(readback))] = len(readback) == len(gen_map) == len(results_df)
        step8_checks["Section-membership, match and diagnostic columns present"] = all(c in readback.columns for c in required_result_columns)
        step8_checks["Every diagnostic column populated (no null / blank values)"] = bool(not (readback.apply(lambda col: col.str.strip() == "").values.any()) and not results_df.isnull().values.any()) if len(readback) > 0 else False
        step8_checks["Matched and mismatched pairs are both present"] = (len(readback[readback["Tables_Match"] == "True"]) == len(results_df) - len(mismatches)) and (len(readback[readback["Tables_Match"] == "False"]) == len(mismatches))
    else:
        for label in ("One row per Generator_name_map pair", "Section-membership, match and diagnostic columns present", "Every diagnostic column populated (no null / blank values)", "Matched and mismatched pairs are both present"):
            step8_checks[label] = False
    step8_checks["Mismatch (exception) file written"] = exceptions_output_path.is_file()
    return results_output_path, exceptions_output_path, step8_checks

def casefold_name(text):
    """Key of the membership indexes: whitespace collapsed, trimmed and case-folded (str.casefold, which also folds characters such as 'ss' / 'ß' that normalize_text's lower() keeps apart)."""
    return re.sub(r"\s+", " ", str(text)).strip().casefold()
def mixed_section_sort_key(section_key):
    """Sort key for mixed section keys: numbered Standard sections first (number, then letter suffix: 3, 3b, 10, 33c), then names (rating periods) alphabetically."""
    section_text = str(section_key)
    number_match = re.match(r"^(\d+)", section_text)
    return (0, int(number_match.group(1)), re.sub(r"^\d+", "", section_text)) if number_match else (1, 0, section_text)
def join_sections(section_keys, empty_text="none"):
    """Section keys as one text in section order ('3, 5, 33c, atc'); empty_text when there is none."""
    return ", ".join(sorted(section_keys, key=mixed_section_sort_key)) if section_keys else empty_text
def parse_section_list(text):
    """Section keys of a written list (the inverse of join_sections); a 'NOT FOUND ...' text means none."""
    return set() if str(text).startswith("NOT FOUND") else set(t.strip() for t in str(text).split(",") if t.strip())
def find_resource_names_workbook(known_paths, defined_path=""):
    """NewPlexosResourceNames workbook: the one already defined in the session when the file still exists, otherwise searched for (never asked): pass 1 = the folders of the known paths and their parents, pass 2 (only when pass 1 finds nothing) = two levels below each of them (never from a drive root or a top-level folder). A .xlsx / .xlsm / .xls file whose name contains 'NewPlexosResourceNames' (the real PlexOS outputs and temporary '~$' files are never picked); the newest match wins. Prints one line. Returns the path ('' when none)."""
    resource_names_path = str(defined_path or "").strip().strip('"').strip("'")
    if resource_names_path != "" and not Path(resource_names_path).is_file():
        print(f"  resource_names_path: '{resource_names_path}' no longer exists - searching again")
        resource_names_path = ""
    resource_names_how = "defined in the session" if resource_names_path != "" else ""
    excel_suffixes = (".xlsx", ".xlsm", ".xls")
    is_names_file = lambda file_name: Path(file_name).suffix.lower() in excel_suffixes and "newplexosresourcenames" in re.sub(r"[^a-z0-9]", "", str(file_name).lower()) and not str(file_name).startswith("~$") and not str(file_name).lower().startswith("plexos_")
    if resource_names_path == "":
        search_base_folders = []
        for known_path in known_paths:
            known_folder = Path(known_path).parent
            for candidate_folder in (known_folder, known_folder.parent):
                if candidate_folder.is_dir() and candidate_folder.resolve() not in search_base_folders:
                    search_base_folders.append(candidate_folder.resolve())
        found_names_files = [found_file for base_folder in search_base_folders for found_file in base_folder.glob("*") if found_file.is_file() and is_names_file(found_file.name)]
        if len(found_names_files) == 0:
            for base_folder in search_base_folders:
                if len(base_folder.parts) < 3:
                    continue
                base_depth = len(base_folder.parts)
                for walk_folder, walk_subfolders, walk_files in os.walk(base_folder):
                    if len(Path(walk_folder).parts) - base_depth >= 2:
                        walk_subfolders[:] = []
                    found_names_files.extend(Path(walk_folder) / walk_file for walk_file in walk_files if is_names_file(walk_file))
        if len(found_names_files) > 0:
            resource_names_path = str(max(found_names_files, key=lambda f: f.stat().st_mtime))
            resource_names_how = f"found automatically ({len(set(found_names_files))} match(es); newest used)"
    print(f"  resource_names_path: {resource_names_path if resource_names_path != '' else '(none found - Step 6 will report Unavailable)'}{'  [' + resource_names_how + ']' if resource_names_how else ''}")
    return resource_names_path
def load_child_names(resource_names_path):
    """The Child Name values (normalized: collapsed whitespace, lower case) of the NewPlexosResourceNames workbook: the first 15 rows of every sheet are searched for the 'Child Name' header. Prints one line. Returns child_names_lower (set), child_names_error ('' when fine)."""
    child_names_lower, child_names_error, child_names_location = set(), "", ""
    if resource_names_path == "":
        child_names_error = ("no NewPlexosResourceNames workbook was found automatically (looked for a .xlsx / .xlsm / .xls file whose name contains 'NewPlexosResourceNames' near the raw data, template, reports and results folder); "
                             "set resource_names_path in the SIT Inputs cell to point to it")
    else:
        try:
            with pd.ExcelFile(resource_names_path) as names_excel:
                found_sheet, found_header_row = None, None
                for sheet_name in names_excel.sheet_names:
                    preview = names_excel.parse(sheet_name, header=None, nrows=15)
                    for row_index in range(len(preview)):
                        if "child name" in [str(v).strip().lower() for v in preview.iloc[row_index].tolist()]:
                            found_sheet, found_header_row = sheet_name, row_index
                            break
                    if found_sheet is not None:
                        break
                if found_sheet is None:
                    child_names_error = "no 'Child Name' header was found in the first 15 rows of any sheet of the NewPlexosResourceNames workbook"
                else:
                    names_frame = names_excel.parse(found_sheet, header=found_header_row)
                    names_frame.columns = [str(c).strip() for c in names_frame.columns]
                    child_column = [c for c in names_frame.columns if c.lower() == "child name"][0]
                    child_names_lower = set(normalize_text(v) for v in names_frame[child_column].dropna().astype(str))
                    child_names_location = f"sheet '{found_sheet}', header on row {found_header_row + 1}"
                    if len(child_names_lower) == 0:
                        child_names_error = "the 'Child Name' column is empty"
        except Exception as exc:
            child_names_error = f"the NewPlexosResourceNames workbook could not be read: {type(exc).__name__}: {exc}"
    print(f"NewPlexosResourceNames: {len(child_names_lower)} Child Name value(s) loaded {('(' + child_names_location + ')') if child_names_location else ''}{'; ERROR: ' + child_names_error if child_names_error else ''}")
    return child_names_lower, child_names_error
def extract_blueprint_sections_with_membership(blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, class_to_raw, property_to_raw_column,
                                               derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """Rebuild EVERY Blueprint_std section from the raw frames (the complete raw membership is needed, not only the relevant sections) like extract_blueprint_sections_keep_null (an all-blank (row, month) stays NULL, it is NOT turned into 0), and in the same pass record what a membership test needs: which report rows are SUMMARY rows (generated labels, not resources), which raw (collection, identifier column) feeds each row and which raw names feed it. Returns extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate, extracted_summary_keys, extracted_key_src, extracted_name_sets, cov_df, table_order, blueprint_titles."""
    extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate = {}, {}, {}, {}, {}
    extracted_summary_keys, extracted_key_src, extracted_name_sets = {}, {}, {}
    coverage_rows, table_order, blueprint_titles, seen_specs = [], [], {}, set()
    df_gen = raw_frames["df_gen"]
    parent_cat = df_gen[df_gen["Collection"] == "Generator"].drop_duplicates("Child Name").set_index("Child Name")["Category"].astype(str).str.strip().str.lower()
    raw_parts = split_frames_by_collection(raw_frames)
    part_key_cache, group_mask_cache, id_str_cache, id_printed_cache, printed_row_cache, child_factor_cache = {}, {}, {}, {}, {}, {}
    for brow in blueprint.to_dict("records"):
        header = brow["Header"]
        tmatch = re.match(r"^\(\s*(\w+)\s*\)", header)
        tkey = tmatch.group(1).lower() if tmatch else header.lower()
        if tkey not in table_order:
            table_order.append(tkey)
            blueprint_titles[tkey] = name_map.get(normalize_text(header), header)
        cls_in, grp_in, prop_in, pattern = brow["Class"], brow["Group"], brow["Property"], brow["Pattern"].lower()
        cls_l, grp_l = cls_in.lower(), grp_in.lower()
        unit_bp = brow["Unit"]
        sign = float(brow["Sign"]) if brow["Sign"] != "" else 1.0
        use_mean = brow["Rate"].strip().lower() in ("true", "1", "yes")
        cov = {"Table": tkey, "Class": cls_in, "Group": grp_in, "Property": prop_in, "Pattern": pattern, "Raw Column": "", "Status": "", "Note": ""}
        spec_id = (header, cls_l, grp_l, prop_in, pattern, unit_bp, sign)
        if spec_id in seen_specs:
            cov["Status"] = "DUPLICATE BLUEPRINT ROW - ignored"
            coverage_rows.append(cov)
            continue
        seen_specs.add(spec_id)
        if tkey in skip_tables:
            cov["Status"], cov["Note"] = "NO COUNTERPART - custom section", skip_tables[tkey]
            coverage_rows.append(cov)
            continue
        if pattern.startswith("daily"):
            cov["Status"], cov["Note"] = "NO COUNTERPART - daily pattern", "Raw workbook is monthly only"
            coverage_rows.append(cov)
            continue
        eff_cls, eff_prop = cls_l, prop_in
        if (tkey, cls_l, prop_in) in custom_overrides:
            eff_cls, eff_prop, cov["Note"] = custom_overrides[(tkey, cls_l, prop_in)]
        if eff_cls not in class_to_raw:
            cov["Status"], cov["Note"] = "NO COUNTERPART - class not in raw data", f"Class '{cls_in}' is not in the raw workbook"
            coverage_rows.append(cov)
            continue
        fkey, coll, id_col = class_to_raw[eff_cls]
        cats, gk = None, None
        if grp_l not in ("all", ""):
            gk = (cls_l, grp_l)
            if gk not in group_assets:
                gk = ("generator", grp_l)
            if gk not in group_assets:
                cov["Status"], cov["Note"] = "UNKNOWN GROUP", f"Class '{cls_in}' + Group '{grp_in}' is not defined on the Groups sheet"
                coverage_rows.append(cov)
                continue
            cats = group_assets[gk]
        printed_summary, generated = None, ""
        if pattern == "monthly-summary":
            gl = "all" if cats is None else group_label.get((cls_l, grp_l), group_label.get(("generator", grp_l), grp_in))
            generated = f"{cls_in}-{gl}-{prop_in}-Total"
            printed_summary = name_map.get(normalize_text(generated), generated)
        derived_components = derived_measures.get((fkey, coll, eff_prop))
        raw_col = None if (eff_cls, eff_prop) in no_raw_notes else property_to_raw_column.get((fkey, coll), {}).get(eff_prop)
        if raw_col is None:
            note_text = no_raw_notes.get((eff_cls, eff_prop), f"No '{eff_prop}' column for {fkey} / {coll}")
            if printed_summary is not None:
                key_only = normalize_text(printed_summary)
                pv_only = pd.DataFrame(np.nan, index=[key_only], columns=month_labels)
                if tkey in extracted:
                    extracted[tkey] = pd.concat([extracted[tkey], pv_only])
                else:
                    extracted[tkey] = pv_only
                    extracted_display[tkey], extracted_names[tkey] = {}, {}
                    extracted_idonly[tkey], extracted_rate[tkey] = set(), use_mean
                extracted_display[tkey][key_only] = printed_summary
                extracted_names[tkey][key_only] = generated
                extracted_idonly[tkey].add(key_only)
                extracted_summary_keys.setdefault(tkey, set()).add(key_only)
                cov["Status"], cov["Note"] = "IDENTIFIER ONLY (no raw measure)", note_text + "; structurally blank raw row"
            else:
                cov["Status"], cov["Note"] = "NO COUNTERPART - no raw measure", note_text
            coverage_rows.append(cov)
            continue
        cov["Raw Column"] = raw_col
        needed_raw_columns = list(derived_components) if derived_components else [raw_col]
        missing_raw_columns = [c for c in needed_raw_columns if c not in raw_frames[fkey].columns]
        if missing_raw_columns:
            cov["Status"] = "NO COUNTERPART - raw column not in the workbook"
            cov["Note"] = f"The raw {fkey} sheet has no column {missing_raw_columns} (columns found: {list(raw_frames[fkey].columns)})"
            print(f"  WARNING: Blueprint row ({header} / {cls_in} / {grp_in} / {prop_in}) reads raw column(s) {missing_raw_columns} that are not on the raw sheet; the row is listed as 'raw column not in the workbook'")
            coverage_rows.append(cov)
            continue
        um = re.search(r"\(([^)]*)\)\s*$", raw_col)
        raw_unit = um.group(1).strip().lower() if um else "-"
        raw_unit = "hours" if raw_unit == "h" else raw_unit
        part = raw_parts.get((fkey, coll))
        if part is None:
            part = raw_frames[fkey].iloc[0:0]
        sub_mask = None
        if cats is not None:
            mask_key = (fkey, coll, gk)
            if mask_key not in group_mask_cache:
                pkey = (fkey, coll)
                if pkey not in part_key_cache:
                    if coll == "Generator.Fuels":
                        kc = part["Parent Name"].map(parent_cat).fillna("")
                        kn = part["Parent Name"].astype(str)
                    else:
                        kc = part["Category"].astype(str).str.strip().str.lower()
                        kn = part["Child Name"].astype(str)
                    part_key_cache[pkey] = (kc, kn.str.replace(r"\s+", " ", regex=True).str.strip())
                key_cat, key_name = part_key_cache[pkey]
                keep_mask = key_cat.isin(cats)
                for rule_cat_l, rule_strings in group_extra_rules.get(gk, []):
                    name_hit = pd.Series(False, index=part.index)
                    for rule_string in rule_strings:
                        name_hit = name_hit | key_name.str.contains(re.escape(rule_string), case=extra_include_match_case, na=False)
                    keep_mask = keep_mask | ((key_cat == rule_cat_l) & name_hit)
                group_mask_cache[mask_key] = keep_mask
            sub_mask = group_mask_cache[mask_key]
        sub = part if sub_mask is None else part[sub_mask]
        sub_value = sub[derived_components].sum(axis=1, min_count=1) if derived_components else sub[raw_col]
        id_key = (fkey, coll, id_col)
        if id_key not in id_str_cache:
            id_str_all = part[id_col].astype(str)
            id_codes, id_uniques = pd.factorize(id_str_all)
            id_printed_list = [name_map.get(normalize_text(s), s) for s in id_uniques]
            id_key_list = [normalize_text(p) for p in id_printed_list]
            id_str_cache[id_key] = id_str_all
            id_printed_cache[id_key] = dict(zip(id_uniques, id_printed_list))
            printed_row_cache[id_key] = (pd.Series(np.array(id_printed_list, dtype=object)[id_codes], index=part.index), pd.Series(np.array(id_key_list, dtype=object)[id_codes], index=part.index))
        id_series = id_str_cache[id_key] if sub_mask is None else id_str_cache[id_key][sub_mask]
        uniq_ids = pd.unique(id_series)
        if printed_summary is not None:
            summary_key = normalize_text(printed_summary)
            key_series = pd.Series(summary_key, index=sub.index)
            dedupe = pd.DataFrame({"k": summary_key, "n": printed_summary, "i": uniq_ids})
            hint_src = printed_summary
        else:
            printed_all, key_all = printed_row_cache[id_key]
            key_series = key_all if sub_mask is None else key_all[sub_mask]
            uniq_printed = [id_printed_cache[id_key][s] for s in uniq_ids]
            dedupe = pd.DataFrame({"k": [normalize_text(p) for p in uniq_printed], "n": uniq_printed, "i": uniq_ids})
            hint_src = header
        hm = re.search(r"\(([^()]*)\)\s*$", hint_src.strip())
        target = unit_bp if unit_bp != "" else (hm.group(1).strip() if hm else raw_unit)
        t_l, f_l, thousand = target.lower().strip(), raw_unit, 1.0
        if t_l.startswith("1000·"):
            t_l, thousand = t_l[len("1000·"):], 1.0 / 1000.0
        t_l = "hours" if t_l == "h" else t_l
        if t_l == f_l:
            factor = 1.0 * thousand
        elif (f_l, t_l) in unit_rules:
            factor = unit_rules[(f_l, t_l)] * thousand
        else:
            factor = None
        if factor is None:
            cov["Status"], cov["Note"] = "NO UNIT RULE", f"UnitConversion has no rule {raw_unit} -> {target}"
            coverage_rows.append(cov)
            continue
        sub_value = sub_value * factor * sign
        if section_special_factor.get(tkey):
            cf_key = (fkey, coll)
            if cf_key not in child_factor_cache:
                child_codes, child_uniques = pd.factorize(part["Child Name"].astype(str))
                child_factors = np.array([contract_factor.get(normalize_text(s), 1.0) for s in child_uniques], dtype=float)
                child_factor_cache[cf_key] = pd.Series(child_factors[child_codes] if len(child_factors) else np.array([], dtype=float), index=part.index)
            cf_all = child_factor_cache[cf_key]
            sub_value = sub_value * (cf_all if sub_mask is None else cf_all[sub_mask])
        work = pd.DataFrame({"Report Key": key_series, "Month Label": sub["Month Label"], "Value": sub_value})
        pv_grouped = work.groupby(["Report Key", "Month Label"])["Value"]
        pv = (pv_grouped.mean() if use_mean else pv_grouped.sum(min_count=1)).dropna().unstack("Month Label")
        pv = pv.reindex(columns=month_labels)
        disp = dedupe.drop_duplicates("k").set_index("k")["n"].to_dict()
        name_sets_here = dedupe.groupby("k")["i"].agg(lambda s: set(str(x) for x in s)).to_dict()
        names = {k: " + ".join(sorted(v)) for k, v in name_sets_here.items()}
        for k, v in name_sets_here.items():
            extracted_key_src.setdefault(tkey, {})[k] = (coll, id_col)
            extracted_name_sets.setdefault(tkey, {}).setdefault(k, set()).update(v)
        if printed_summary is not None:
            extracted_summary_keys.setdefault(tkey, set()).update(list(pv.index))
        if tkey in extracted:
            extracted[tkey] = extracted[tkey].add(pv, fill_value=0.0)
            extracted_display[tkey].update({k: v for k, v in disp.items() if k not in extracted_display[tkey]})
            for k, v in names.items():
                extracted_names[tkey][k] = (extracted_names[tkey][k] + " + " + v) if k in extracted_names[tkey] else v
        else:
            extracted[tkey] = pv
            extracted_display[tkey] = dict(disp)
            extracted_names[tkey] = names
            extracted_idonly[tkey] = set()
            extracted_rate[tkey] = use_mean
        cov["Status"] = "EXTRACTED" if not derived_components else "EXTRACTED (derived measure)"
        coverage_rows.append(cov)
    table_order.sort(key=section_sort_key)
    return extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate, extracted_summary_keys, extracted_key_src, extracted_name_sets, pd.DataFrame(coverage_rows), table_order, blueprint_titles
def parse_membership_reports(reports, relevant_standard_tables, ratings_key_aliases, table_order, used_in_datamodel_tables=None):
    """Parse both PLEXOS reports for a membership test. Standard: EVERY section is parsed ('PLEXOS_tables_all' = all sections, as discovered; 'PLEXOS_tables' = the relevant ones, the working copy the rest of the block trims). When used_in_datamodel_tables is given the working copy and the raw tables / table_order are also restricted to the Used in DataModel sections. Ratings: 'PLEXOS_tables' = the sections after the approved aliases (sections that resolve to the same key are merged), 'PLEXOS_tables_all' = a copy of them, 'PLEXOS_discovered_keys_raw' = the keys as discovered (before the aliases). Updates reports and table_order in place; prints the same lines as the other blocks."""
    for report_name, report_config in reports.items():
        plexos_tables, plexos_format_issues, _, discovered_section_keys = parse_plexos_report_sections(plexos_rows=report_config["PLEXOS_rows"], report_name=report_name, in_scope_tables=None)
        report_config["PLEXOS_format_issues"] = plexos_format_issues
        report_config["PLEXOS_discovered_keys_raw"] = list(discovered_section_keys)
        raw_count = lambda: len(reports[report_name]["Raw_tables"])
        if report_name == "Standard Report":
            report_config["PLEXOS_tables_all"] = {key: {"title": value["title"], "data": value["data"]} for key, value in plexos_tables.items()}
            plexos_tables = {key: value for key, value in plexos_tables.items() if key in relevant_standard_tables}
            if used_in_datamodel_tables is not None:
                plexos_dropped = sorted(set(plexos_tables) - used_in_datamodel_tables, key=section_sort_key)
                plexos_tables = filter_tables_by_keys(plexos_tables, used_in_datamodel_tables)
                reports[report_name]["Raw_tables"] = filter_tables_by_keys(reports[report_name]["Raw_tables"], used_in_datamodel_tables)
                table_order[:] = [table_key for table_key in table_order if table_key in used_in_datamodel_tables]
                print(f"[{report_name}] Tables kept (in scope and Used in DataModel): Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
                if plexos_dropped:
                    print(f"[{report_name}] In-scope PLEXOS table(s) dropped (not marked 'Used in DataModel'): {plexos_dropped}")
            else:
                print(f"[{report_name}] 'Used in DataModel' filter skipped -- all in-scope sections kept: Raw={raw_count()}, PLEXOS={len(plexos_tables)}")
        else:
            print(f"[{report_name}] 'Used in DataModel' filter skipped (not applicable to named sections) -- all sections kept: Raw={raw_count()} (no raw counterpart), PLEXOS={len(plexos_tables)}")
            print(f"[{report_name}] PLEXOS section keys found (raw, pre-alias): {sorted(plexos_tables.keys())}")
            plexos_tables, _ = apply_section_aliases(plexos_tables, ratings_key_aliases)
            report_config["PLEXOS_tables_all"] = {key: {"title": value["title"], "data": value["data"]} for key, value in plexos_tables.items()}
            print(f"[{report_name}] PLEXOS section keys: {sorted(plexos_tables.keys())}")
        report_config["PLEXOS_tables"] = plexos_tables
def build_raw_membership_index(raw_tables, summary_keys_by_table, key_src_by_table, name_sets_by_table, resource_sources, rating_raw_tables, name_map):
    """RAW side (solution.zip): resource name -> the set of sections it feeds, from the normalized raw sections (every Blueprint section, so the complete membership is known). Only resource rows count: summary rows (generated labels) and rows whose identifier is not one of resource_sources (for example Region and contract-fuel rows) are skipped. When rating-period raw tables exist their rows give the rating membership (the printed names are also mapped back to the Plexos names they replace). Two indexes: exact (the name as stored) and normalized (casefold_name). Returns raw_exact_to_tables, raw_norm_to_tables, raw_resource_rows, summary_rows_skipped, non_resource_rows_skipped."""
    raw_exact_to_tables, raw_norm_to_tables = {}, {}
    resource_rows = summary_skipped = non_resource_skipped = 0
    for table_number, entry in raw_tables.items():
        data = entry["data"]
        if data.shape[1] == 0:
            continue
        summary_keys, key_src, name_sets = summary_keys_by_table.get(table_number, set()), key_src_by_table.get(table_number, {}), name_sets_by_table.get(table_number, {})
        for printed in data.iloc[:, 0].fillna("").astype(str).tolist():
            row_key = normalize_text(printed)
            if row_key == "":
                continue
            if row_key in summary_keys:
                summary_skipped += 1
                continue
            if key_src.get(row_key) not in resource_sources:
                non_resource_skipped += 1
                continue
            resource_rows += 1
            for raw_name in name_sets.get(row_key, set()):
                raw_exact_to_tables.setdefault(str(raw_name).strip(), set()).add(table_number)
                raw_norm_to_tables.setdefault(casefold_name(raw_name), set()).add(table_number)
    if len(rating_raw_tables) > 0:
        printed_to_plexos = {}
        for plexos_lower, printed_name in name_map.items():
            printed_to_plexos.setdefault(casefold_name(printed_name), set()).add(plexos_lower)
        for rating_key, entry in rating_raw_tables.items():
            data = entry["data"]
            if data.shape[1] == 0:
                continue
            for printed in data.iloc[:, 0].fillna("").astype(str).tolist():
                for candidate in {printed.strip(), printed.split(":")[0].strip()}:
                    if candidate == "":
                        continue
                    candidate_key = casefold_name(candidate)
                    raw_exact_to_tables.setdefault(candidate, set()).add(rating_key)
                    raw_norm_to_tables.setdefault(candidate_key, set()).add(rating_key)
                    for plexos_lower in printed_to_plexos.get(candidate_key, set()):
                        raw_exact_to_tables.setdefault(plexos_lower, set()).add(rating_key)
                        raw_norm_to_tables.setdefault(casefold_name(plexos_lower), set()).add(rating_key)
    return raw_exact_to_tables, raw_norm_to_tables, resource_rows, summary_skipped, non_resource_skipped
def build_output_membership_index(reports, relevant_standard_set, relevant_rating_sections, ratings_have_raw):
    """OUTPUT side (Plexos_to_reporting): row title -> the set of sections it is printed in, from EVERY section discovered in the Standard and Ratings reports ('PLEXOS_tables_all'; Total, blank and (Primary) / (Secondary) / (Startup) / (Topping) sub-rows are not resources; a rating row title 'Plant CC A:MW' is also indexed as 'Plant CC A'). Two indexes: exact and normalized (casefold_name). Returns out_exact_to_tables, out_norm_to_tables and discovery_rows (one record per discovered section)."""
    out_exact_to_tables, out_norm_to_tables, discovery_rows = {}, {}, []
    for report_name in ["Standard Report", "Ratings Report"]:
        for section_key, entry in reports[report_name]["PLEXOS_tables_all"].items():
            data = entry["data"]
            label_series = data.iloc[:, 0].fillna("").astype(str) if data.shape[1] > 0 else pd.Series([], dtype=str)
            resource_rows = 0
            for printed in label_series.tolist():
                label_norm = normalize_text(printed)
                if label_norm == "" or label_norm == "total" or label_norm.startswith("("):
                    continue
                resource_rows += 1
                candidates = {printed.strip()} | ({printed.split(":")[0].strip()} if report_name == "Ratings Report" else set())
                for candidate in candidates:
                    if candidate == "":
                        continue
                    out_exact_to_tables.setdefault(candidate, set()).add(section_key)
                    out_norm_to_tables.setdefault(casefold_name(candidate), set()).add(section_key)
            is_relevant = section_key in relevant_standard_set if report_name == "Standard Report" else section_key in set(relevant_rating_sections)
            discovery_rows.append({"Report": report_name, "Section": section_key, "Title": entry["title"], "Data Rows": int(len(data)), "Row Labels (resources)": resource_rows, "Relevant Section": is_relevant,
                                   "Compared Against Raw Data": bool(is_relevant and (report_name == "Standard Report" or ratings_have_raw))})
    return out_exact_to_tables, out_norm_to_tables, discovery_rows
def discover_report_sections(plexos_sr_rows, plexos_rr_rows, reports, ratings_key_aliases, relevant_standard_tables, relevant_rating_sections, discovery_rows):
    """Step 2: the sections of both reports discovered by two independent methods that must agree: a header-pattern line scan of the report text and the structural parse ('PLEXOS_tables_all'). A section with a header but no data rows is listed (discovered, not lost). Returns a dictionary with the discovered / relevant / not relevant / lost / header-only section lists and discovery_df (the discovery_rows plus the header-only sections, sorted)."""
    section_header_re = re.compile(r"^\s*\(\s*([0-9]+[a-zA-Z]?)\s*\)\s*(.+?)\s*$")
    scan_standard = set()
    for row in plexos_sr_rows:
        if len(row) == 0 or not str(row[0]).lstrip().startswith("("):
            continue
        line_text = ",".join(str(cell) for cell in row)
        header_match = section_header_re.match(line_text.rstrip(","))
        if header_match and "=" not in line_text:
            scan_standard.add(header_match.group(1).lower())
    day_pattern = r"(?:mon|tue|tues|wed|weds|thu|thur|thurs|fri|sat|sun|sunday|monday|tuesday|wednesday|thursday|friday|saturday)"
    scan_ratings = set()
    for row in plexos_rr_rows:
        non_blank_cells = [cell_text for cell_text in (str(cell).strip() for cell in row) if cell_text]
        if len(non_blank_cells) == 1:
            rating_text = re.sub(r"\([^)]*\)", "", non_blank_cells[0].lower().strip())
            rating_text = re.sub(rf"\b{day_pattern}\s*-\s*{day_pattern}\b", "", rating_text)
            rating_text = re.sub(r"[^a-z0-9]+", "", rating_text)
            scan_ratings.add(ratings_key_aliases.get(rating_text, rating_text))
    parsed_standard, parsed_ratings = set(reports["Standard Report"]["PLEXOS_tables_all"].keys()), set(reports["Ratings Report"]["PLEXOS_tables_all"].keys())
    ordered = lambda keys: sorted(keys, key=mixed_section_sort_key)
    discovered_standard, discovered_ratings = ordered(scan_standard | parsed_standard), ordered(scan_ratings | parsed_ratings)
    rating_relevant_set = set(relevant_rating_sections)
    found = {"discovered_standard": discovered_standard, "discovered_ratings": discovered_ratings, "standard_lost": ordered(parsed_standard - scan_standard), "ratings_lost": ordered(parsed_ratings - scan_ratings),
             "standard_headers_only": ordered(scan_standard - parsed_standard), "ratings_headers_only": ordered(scan_ratings - parsed_ratings),
             "standard_relevant_found": [t for t in discovered_standard if t in relevant_standard_tables], "standard_not_relevant": [t for t in discovered_standard if t not in relevant_standard_tables],
             "standard_relevant_absent": [t for t in relevant_standard_tables if t not in discovered_standard], "rating_relevant_found": [t for t in discovered_ratings if t in rating_relevant_set],
             "rating_not_relevant": [t for t in discovered_ratings if t not in rating_relevant_set]}
    all_rows = list(discovery_rows)
    for report_name, header_only_keys, relevant_keys in (("Standard Report", found["standard_headers_only"], set(relevant_standard_tables)), ("Ratings Report", found["ratings_headers_only"], rating_relevant_set)):
        for header_only_key in header_only_keys:
            all_rows.append({"Report": report_name, "Section": header_only_key, "Title": "(header found, no data rows)", "Data Rows": 0, "Row Labels (resources)": 0, "Relevant Section": header_only_key in relevant_keys, "Compared Against Raw Data": False})
    discovery_df = pd.DataFrame(all_rows)
    discovery_df["Section Sort"] = [mixed_section_sort_key(str(s)) for s in discovery_df["Section"]]
    found["discovery_df"] = discovery_df.sort_values(by=["Report", "Section Sort"]).drop(columns=["Section Sort"]).reset_index(drop=True)
    return found
def check_mismatch_flags(mismatches, child_names_lower):
    """Step 6: every mismatched pair has a Yes / No answer (never blank) and each answer equals the independent lookup of Resources_Plexos in the Child Name set (a blank name is always No). Returns every_flag_valid, rederived_ok."""
    every_flag_valid = bool(mismatches.empty or mismatches["Resources_Plexos_In_NewPlexosResourceNames"].isin(["Yes", "No"]).all())
    rederived_ok = True
    for mismatch_row in mismatches.to_dict("records"):
        expected_flag = "No" if mismatch_row["Resources_Plexos"] == "(blank)" else ("Yes" if casefold_name(mismatch_row["Resources_Plexos"]) in child_names_lower else "No")
        if mismatch_row["Resources_Plexos_In_NewPlexosResourceNames"] != expected_flag:
            rederived_ok = False
    return every_flag_valid, rederived_ok

################################################################################################################################################################################
#3.07
################################################################################################################################################################################
def rebuild_tables_without_excluded_names_unit_aligned(table_keys, excluded_names_by_fragment, extracted_parts, blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                                                       class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """PlexOS-3.07 version of rebuild_tables_without_excluded_names (3.03C / 3.03D): a raw unit that PLEXOS does not print must not be added into a SUMMARY table either (Table 1 adds every unit of a group, so Novo BioPower was added to
    'Wind/Solar Generation (MWH)' and 'Wind/Solar Total Costs ($)'). extracted_parts = (extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate, extracted_source, unit_alignment); the rebuilt tables replace the old ones in place."""
    import io, contextlib
    collapse = lambda text: re.sub(r"\s+", " ", str(text)).strip()
    report_columns = ["Table", "Row", "Excluded Raw Name(s) Removed", "Months Changed", "Sum Of Monthly Values Before", "Sum Of Monthly Values After", "Removed", "Status"]
    excluded_names = sorted(set(n for names in excluded_names_by_fragment.values() for n in names))
    if len(excluded_names) == 0:
        print("  Excluded raw units: none found, so no summary table is rebuilt")
        return pd.DataFrame(columns=report_columns)
    excluded_keys = set(collapse(n) for n in excluded_names)
    filtered_frames = {}
    for frame_key, frame in raw_frames.items():
        child_hit = frame["Child Name"].map(collapse).isin(excluded_keys)
        parent_hit = frame["Parent Name"].map(collapse).isin(excluded_keys) if "Parent Name" in frame.columns else child_hit & False
        fuel_rows = frame["Collection"].astype(str).str.startswith("Generator.")
        filtered_frames[frame_key] = frame[~((child_hit & ~fuel_rows) | (parent_hit & fuel_rows))]
    removed_rows = {k: len(raw_frames[k]) - len(filtered_frames[k]) for k in raw_frames}
    print(f"  Rebuilding summary table(s) {list(table_keys)} without {excluded_names}: raw rows left out {removed_rows}")
    old_tables = {t: extracted_parts[0][t].copy() for t in table_keys if t in extracted_parts[0]}
    old_names = {t: dict(extracted_parts[2].get(t, {})) for t in old_tables}
    with contextlib.redirect_stdout(io.StringIO()):
        rebuilt = extract_blueprint_sections_unit_aligned(blueprint, filtered_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, list(table_keys), class_to_raw,
                                                          property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case)
    report_rows = []
    for table_key in table_keys:
        if table_key not in old_tables or table_key not in rebuilt[0]:
            print(f"  PROBLEM: table {table_key} is not in the extraction, so it was not rebuilt")
            report_rows.append({"Table": table_key, "Row": "(whole table)", "Excluded Raw Name(s) Removed": "", "Months Changed": 0, "Sum Of Monthly Values Before": np.nan, "Sum Of Monthly Values After": np.nan, "Removed": np.nan, "Status": "NOT REPLACED: table not in the extraction"})
            continue
        old_frame, new_frame = old_tables[table_key], rebuilt[0][table_key]
        if list(old_frame.index) != list(new_frame.index) or list(old_frame.columns) != list(new_frame.columns):
            print(f"  PROBLEM: table {table_key} has different rows or month columns without the excluded units, so it was NOT replaced (the earlier values are kept)")
            report_rows.append({"Table": table_key, "Row": "(whole table)", "Excluded Raw Name(s) Removed": "", "Months Changed": 0, "Sum Of Monthly Values Before": np.nan, "Sum Of Monthly Values After": np.nan, "Removed": np.nan, "Status": "NOT REPLACED: rows or month columns differ"})
            continue
        for part_position in range(7):
            if table_key in rebuilt[part_position]:
                extracted_parts[part_position][table_key] = rebuilt[part_position][table_key]
        old_values, new_values = old_frame.to_numpy(dtype=float), new_frame.to_numpy(dtype=float)
        same_cell = np.isclose(np.nan_to_num(old_values), np.nan_to_num(new_values), rtol=0.0, atol=1e-9) & (np.isnan(old_values) == np.isnan(new_values))
        for row_position in np.flatnonzero(~same_cell.all(axis=1)):
            row_key = old_frame.index[row_position]
            old_listed = set(collapse(n) for n in str(old_names[table_key].get(row_key, "")).split(" + "))
            new_listed = set(collapse(n) for n in str(extracted_parts[2][table_key].get(row_key, "")).split(" + "))
            removed_here = sorted(n for n in excluded_names if collapse(n) in old_listed and collapse(n) not in new_listed)
            before, after = float(np.nansum(old_values[row_position])), float(np.nansum(new_values[row_position]))
            report_rows.append({"Table": table_key, "Row": str(extracted_parts[1][table_key].get(row_key, row_key)).strip(), "Excluded Raw Name(s) Removed": " + ".join(removed_here), "Months Changed": int((~same_cell[row_position]).sum()),
                                "Sum Of Monthly Values Before": before, "Sum Of Monthly Values After": after, "Removed": before - after, "Status": "REPLACED"})
    report = pd.DataFrame(report_rows, columns=report_columns)
    for _, report_row in report[report["Status"] == "REPLACED"].iterrows():
        print(f"    Table {report_row['Table']} '{report_row['Row']}': {report_row['Excluded Raw Name(s) Removed']} removed from {int(report_row['Months Changed'])} month(s); sum of the monthly values {report_row['Sum Of Monthly Values Before']:,.1f} -> {report_row['Sum Of Monthly Values After']:,.1f}")
    if report[report["Status"] == "REPLACED"].empty and report[report["Status"] != "REPLACED"].empty:
        print("    No value in the rebuilt table(s) changed: the excluded units were not part of any summary row")
    return report
def extract_blueprint_sections_unit_aligned_by_section_map(blueprint, section_name_maps, section_headers, default_name_map, raw_frames, month_labels, group_assets, group_label, group_extra_rules, unit_rules, contract_factor,
                                                           in_scope_tables, class_to_raw, property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """extract_blueprint_sections_unit_aligned, run once per name map: the Blueprint_std rows of the sections that name a section-only maptable_ sheet (section_headers: Table 23 = maptable_Contracts, Table 26 = maptable_Contracts_Cost) are rebuilt with that section's name map
    (section_name_maps), every other row with default_name_map. The results are merged and returned exactly like extract_blueprint_sections_unit_aligned (the per-part 'Scope' line is replaced by ONE line for the merged result; every other printed line, such as a raw-column warning, is kept)."""
    import io, contextlib
    map_key_by_row = blueprint["Header"].map(lambda header_text: section_headers.get(header_text, ()))
    keys_in_order = list(dict.fromkeys(map_key_by_row.tolist()))
    merged = [{}, {}, {}, {}, {}, {}, {}]
    coverage_frames, out_of_scope_tables, blueprint_titles, tables_seen, printed_lines = [], set(), {}, [], []
    for map_key in keys_in_order:
        part_blueprint = blueprint[map_key_by_row.map(lambda row_key: row_key == map_key)]
        part_name_map = default_name_map if map_key == () else section_name_maps[map_key][0]
        part_output = io.StringIO()
        with contextlib.redirect_stdout(part_output):
            part = extract_blueprint_sections_unit_aligned(part_blueprint, raw_frames, month_labels, part_name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, in_scope_tables, class_to_raw,
                                                           property_to_raw_column, derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case)
        printed_lines.extend(line for line in part_output.getvalue().splitlines() if not line.strip().startswith(("Scope:", "WARNING: in-scope section(s) not found")))
        for position in range(7):
            merged[position].update(part[position])
        coverage_frames.append(part[7])
        out_of_scope_tables |= set(part[9])
        blueprint_titles.update(part[10])
        tables_seen.extend(t for t in part[8] if t not in tables_seen)
    for line in dict.fromkeys(printed_lines):
        print(line)
    table_order = sorted(tables_seen, key=section_sort_key)
    cov_df = pd.concat(coverage_frames, ignore_index=True)
    scope_missing_from_blueprint = [t for t in in_scope_tables if t not in table_order]
    print(f"  Scope: {len(in_scope_tables)} Standard sections in scope; {len(out_of_scope_tables)} Blueprint_std sections outside the scope were excluded; {sum(1 for k in keys_in_order if k != ())} section-only maptable_ sheet(s) applied")
    if scope_missing_from_blueprint:
        print(f"  WARNING: in-scope section(s) not found in Blueprint_std: {scope_missing_from_blueprint}")
    return (merged[0], merged[1], merged[2], merged[3], merged[4], merged[5], merged[6], cov_df, table_order, out_of_scope_tables, blueprint_titles)
def exclude_all_zero_raw_only_rows(standard_config, table_keys, extracted_names, month_labels):
    """Drop raw rows that PLEXOS does NOT print AND whose every monthly value is zero (a resource in the raw model that never carries a value, e.g. an expansion battery that is not built: there is nothing to compare and nothing to print).
    A row with no numeric value at all (identifier only) is not touched. table_keys = tables to look at (None = every raw table). Updates the raw tables in place. Returns a DataFrame in the layout of exclude_raw_only_rows (so both logs can be written to one CSV)."""
    exclusion_rows = []
    for table_number in (table_keys if table_keys is not None else list(standard_config["Raw_tables"].keys())):
        if table_number not in standard_config["Raw_tables"] or table_number not in standard_config["PLEXOS_tables"]:
            continue
        raw_data = standard_config["Raw_tables"][table_number]["data"]
        px_norm = set(normalize_series(standard_config["PLEXOS_tables"][table_number]["data"].iloc[:, 0]))
        names_lookup = extracted_names.get(table_number, {})
        month_columns = [c for c in month_labels if c in raw_data.columns]
        if len(month_columns) == 0 or len(raw_data) == 0:
            continue
        values = raw_data[month_columns].apply(pd.to_numeric, errors="coerce")
        drop_mask = pd.Series(False, index=raw_data.index)
        for raw_index, raw_key in normalize_series(raw_data.iloc[:, 0]).items():
            if raw_key == "" or raw_key in px_norm:
                continue
            row_values = values.loc[raw_index].dropna()
            if len(row_values) > 0 and (row_values.abs() <= 1e-12).all():
                drop_mask[raw_index] = True
                exclusion_rows.append({"Table Number": table_number, "Raw Row Title": raw_data.loc[raw_index, raw_data.columns[0]], "Raw Data Name(s)": names_lookup.get(raw_key, ""),
                                       "Matched Rule": f"every monthly value is zero ({len(row_values)} month(s))", "Reason": "Raw-only row with no values at all that PLEXOS does not print (nothing to compare)"})
        standard_config["Raw_tables"][table_number]["data"] = raw_data[~drop_mask].reset_index(drop=True)
    return pd.DataFrame(exclusion_rows, columns=["Table Number", "Raw Row Title", "Raw Data Name(s)", "Matched Rule", "Reason"])
def rating_expand_sections(raw_tables, px_tables, section_keys):
    expanded_sections = []
    for section_key in section_keys:
        raw_section, px_section = raw_tables.get(section_key), px_tables.get(section_key)
        missing_reason = rating_no_raw_notes.get(section_key, rating_no_raw_default) if len(raw_ratings_tables) > 0 else RATINGS_NO_RAW_REASON
        if raw_section is None or px_section is None:
            expanded_sections.append((section_key, raw_section, px_section, missing_reason))
            continue
        seen_aliases = set()
        for rating_definition in rating_definitions:
            alias_text, measure_text = rating_definition["alias"], rating_definition["measure"]
            if alias_text.lower() in seen_aliases:
                continue                                        #an alias with two definitions (Var O&M: Generator + Battery) is ONE section: its rows are selected by the alias
            seen_aliases.add(alias_text.lower())
            basis_label_text, basis_column_text = rating_alias_basis(rating_definitions, alias_text, RATING_UNIT_FACTOR)
            alias_suffix = ":" + alias_text.lower()
            alias_rows = lambda frame: frame[frame.iloc[:, 0].fillna("").astype(str).str.strip().str.lower().str.endswith(alias_suffix)].reset_index(drop=True)
            raw_alias_part, px_alias_part = alias_rows(raw_section["data"]), alias_rows(px_section["data"])
            if len(raw_alias_part) == 0 and len(px_alias_part) == 0:
                continue
            alias_title = f"{px_section['title']} :{alias_text} rows (raw {basis_label_text})"
            alias_label = f"{section_key} ({alias_text})"
            rating_alignment_texts[alias_label] = f"{basis_column_text} -> report units ({alias_text} rows)"
            expanded_sections.append((alias_label, {"title": alias_title, "data": raw_alias_part}, {"title": alias_title, "data": px_alias_part}, missing_reason))
    return expanded_sections
def extract_blueprint_sections_unit_aligned(blueprint, raw_frames, month_labels, name_map, group_assets, group_label, group_extra_rules, unit_rules, contract_factor, in_scope_tables, class_to_raw, property_to_raw_column,
                                            derived_measures, no_raw_notes, custom_overrides, skip_tables, section_special_factor, extra_include_match_case):
    """Rebuild the in-scope Standard Report sections from the raw frames (same arguments as extract_blueprint_sections_keep_null) for a test that PRINTS and CLASSIFIES by the monthly sums: a (row, month) whose raw values are ALL blank stays NULL (it is NOT turned into 0) and the arithmetic stays bit-for-bit identical: a group with ONE raw value is its own value and every group with SEVERAL raw values is added with the same per-group Series.sum(min_count=1) / Series.mean call. It also records the UNIT ALIGNMENT of every section ('gwh -> mwh (x1000)') and the (raw collection, identifier column) the identifiers come from. Returns extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate, extracted_source, unit_alignment, cov_df, table_order, out_of_scope_tables, blueprint_titles."""
    extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate, extracted_source, unit_alignment = {}, {}, {}, {}, {}, {}, {}
    coverage_rows, table_order, out_of_scope_tables, blueprint_titles, seen_specs = [], [], set(), {}, set()
    df_gen = raw_frames["df_gen"]
    parent_cat = df_gen[df_gen["Collection"] == "Generator"].drop_duplicates("Child Name").set_index("Child Name")["Category"].astype(str).str.strip().str.lower()
    raw_parts = split_frames_by_collection(raw_frames)
    part_key_cache, group_mask_cache, id_str_cache, id_printed_cache, printed_row_cache, child_factor_cache = {}, {}, {}, {}, {}, {}
    for brow in blueprint.to_dict("records"):
        header = brow["Header"]
        tmatch = re.match(r"^\(\s*(\w+)\s*\)", header)
        tkey = tmatch.group(1).lower() if tmatch else header.lower()
        if tkey not in in_scope_tables:
            out_of_scope_tables.add(tkey)
            continue
        if tkey not in table_order:
            table_order.append(tkey)
            blueprint_titles[tkey] = name_map.get(normalize_text(header), header)
        cls_in, grp_in, prop_in, pattern = brow["Class"], brow["Group"], brow["Property"], brow["Pattern"].lower()
        cls_l, grp_l = cls_in.lower(), grp_in.lower()
        unit_bp = brow["Unit"]
        sign = float(brow["Sign"]) if brow["Sign"] != "" else 1.0
        use_mean = brow["Rate"].strip().lower() in ("true", "1", "yes")
        cov = {"Table": tkey, "Class": cls_in, "Group": grp_in, "Property": prop_in, "Pattern": pattern, "Raw Column": "", "Status": "", "Note": ""}
        spec_id = (header, cls_l, grp_l, prop_in, pattern, unit_bp, sign)
        if spec_id in seen_specs:
            cov["Status"] = "DUPLICATE BLUEPRINT ROW - ignored"
            coverage_rows.append(cov)
            continue
        seen_specs.add(spec_id)
        if tkey in skip_tables:
            cov["Status"], cov["Note"] = "NO COUNTERPART - custom section", skip_tables[tkey]
            coverage_rows.append(cov)
            continue
        if pattern.startswith("daily"):
            cov["Status"], cov["Note"] = "NO COUNTERPART - daily pattern", "Raw workbook is monthly only"
            coverage_rows.append(cov)
            continue
        eff_cls, eff_prop = cls_l, prop_in
        if (tkey, cls_l, prop_in) in custom_overrides:
            eff_cls, eff_prop, cov["Note"] = custom_overrides[(tkey, cls_l, prop_in)]
        if eff_cls not in class_to_raw:
            cov["Status"], cov["Note"] = "NO COUNTERPART - class not in raw data", f"Class '{cls_in}' is not in the raw workbook"
            coverage_rows.append(cov)
            continue
        fkey, coll, id_col = class_to_raw[eff_cls]
        cats, gk = None, None
        if grp_l not in ("all", ""):
            gk = (cls_l, grp_l)
            if gk not in group_assets:
                gk = ("generator", grp_l)
            if gk not in group_assets:
                cov["Status"], cov["Note"] = "UNKNOWN GROUP", f"Class '{cls_in}' + Group '{grp_in}' is not defined on the Groups sheet"
                coverage_rows.append(cov)
                continue
            cats = group_assets[gk]
        printed_summary, generated = None, ""
        if pattern == "monthly-summary":
            gl = "all" if cats is None else group_label.get((cls_l, grp_l), group_label.get(("generator", grp_l), grp_in))
            generated = f"{cls_in}-{gl}-{prop_in}-Total"
            printed_summary = name_map.get(normalize_text(generated), generated)
        derived_components = derived_measures.get((fkey, coll, eff_prop))
        raw_col = None if (eff_cls, eff_prop) in no_raw_notes else property_to_raw_column.get((fkey, coll), {}).get(eff_prop)
        if raw_col is None:
            note_text = no_raw_notes.get((eff_cls, eff_prop), f"No '{eff_prop}' column for {fkey} / {coll}")
            if printed_summary is not None:
                key_only = normalize_text(printed_summary)
                pv_only = pd.DataFrame(np.nan, index=[key_only], columns=month_labels)
                if tkey in extracted:
                    extracted[tkey] = pd.concat([extracted[tkey], pv_only])
                else:
                    extracted[tkey] = pv_only
                    extracted_display[tkey], extracted_names[tkey] = {}, {}
                    extracted_idonly[tkey], extracted_rate[tkey] = set(), use_mean
                extracted_display[tkey][key_only] = printed_summary
                extracted_names[tkey][key_only] = generated
                extracted_idonly[tkey].add(key_only)
                cov["Status"], cov["Note"] = "IDENTIFIER ONLY (no raw measure)", note_text + "; structurally blank raw row"
            else:
                cov["Status"], cov["Note"] = "NO COUNTERPART - no raw measure", note_text
            coverage_rows.append(cov)
            continue
        cov["Raw Column"] = raw_col
        needed_raw_columns = list(derived_components) if derived_components else [raw_col]
        missing_raw_columns = [c for c in needed_raw_columns if c not in raw_frames[fkey].columns]
        if missing_raw_columns:
            cov["Status"] = "NO COUNTERPART - raw column not in the workbook"
            cov["Note"] = f"The raw {fkey} sheet has no column {missing_raw_columns} (columns found: {list(raw_frames[fkey].columns)})"
            print(f"  WARNING: Blueprint row ({header} / {cls_in} / {grp_in} / {prop_in}) reads raw column(s) {missing_raw_columns} that are not on the raw sheet; the row is listed as 'raw column not in the workbook'")
            coverage_rows.append(cov)
            continue
        um = re.search(r"\(([^)]*)\)\s*$", raw_col)
        raw_unit = um.group(1).strip().lower() if um else "-"
        raw_unit = "hours" if raw_unit == "h" else raw_unit
        part = raw_parts.get((fkey, coll))
        if part is None:
            part = raw_frames[fkey].iloc[0:0]
        sub_mask = None
        if cats is not None:
            mask_key = (fkey, coll, gk)
            if mask_key not in group_mask_cache:
                pkey = (fkey, coll)
                if pkey not in part_key_cache:
                    if coll == "Generator.Fuels":
                        kc = part["Parent Name"].map(parent_cat).fillna("")
                        kn = part["Parent Name"].astype(str)
                    else:
                        kc = part["Category"].astype(str).str.strip().str.lower()
                        kn = part["Child Name"].astype(str)
                    part_key_cache[pkey] = (kc, kn.str.replace(r"\s+", " ", regex=True).str.strip())
                key_cat, key_name = part_key_cache[pkey]
                keep_mask = key_cat.isin(cats)
                for rule_cat_l, rule_strings in group_extra_rules.get(gk, []):
                    name_hit = pd.Series(False, index=part.index)
                    for rule_string in rule_strings:
                        name_hit = name_hit | key_name.str.contains(re.escape(rule_string), case=extra_include_match_case, na=False)
                    keep_mask = keep_mask | ((key_cat == rule_cat_l) & name_hit)
                group_mask_cache[mask_key] = keep_mask
            sub_mask = group_mask_cache[mask_key]
        sub = part if sub_mask is None else part[sub_mask]
        sub_value = sub[derived_components].sum(axis=1, min_count=1) if derived_components else sub[raw_col]
        id_key = (fkey, coll, id_col)
        if id_key not in id_str_cache:
            id_str_all = part[id_col].astype(str)
            id_codes, id_uniques = pd.factorize(id_str_all)
            id_printed_list = [name_map.get(normalize_text(s), s) for s in id_uniques]
            id_key_list = [normalize_text(p) for p in id_printed_list]
            id_str_cache[id_key] = id_str_all
            id_printed_cache[id_key] = dict(zip(id_uniques, id_printed_list))
            printed_row_cache[id_key] = (pd.Series(np.array(id_printed_list, dtype=object)[id_codes], index=part.index), pd.Series(np.array(id_key_list, dtype=object)[id_codes], index=part.index))
        id_series = id_str_cache[id_key] if sub_mask is None else id_str_cache[id_key][sub_mask]
        uniq_ids = pd.unique(id_series)
        if printed_summary is not None:
            summary_key = normalize_text(printed_summary)
            key_series = pd.Series(summary_key, index=sub.index)
            dedupe = pd.DataFrame({"k": summary_key, "n": printed_summary, "i": uniq_ids})
            hint_src = printed_summary
        else:
            printed_all, key_all = printed_row_cache[id_key]
            key_series = key_all if sub_mask is None else key_all[sub_mask]
            uniq_printed = [id_printed_cache[id_key][s] for s in uniq_ids]
            dedupe = pd.DataFrame({"k": [normalize_text(p) for p in uniq_printed], "n": uniq_printed, "i": uniq_ids})
            hint_src = header
        hm = re.search(r"\(([^()]*)\)\s*$", hint_src.strip())
        target = unit_bp if unit_bp != "" else (hm.group(1).strip() if hm else raw_unit)
        t_l, f_l, thousand = target.lower().strip(), raw_unit, 1.0
        if t_l.startswith("1000·"):
            t_l, thousand = t_l[len("1000·"):], 1.0 / 1000.0
        t_l = "hours" if t_l == "h" else t_l
        if t_l == f_l:
            factor = 1.0 * thousand
        elif (f_l, t_l) in unit_rules:
            factor = unit_rules[(f_l, t_l)] * thousand
        else:
            factor = None
        if factor is None:
            cov["Status"], cov["Note"] = "NO UNIT RULE", f"UnitConversion has no rule {raw_unit} -> {target}"
            coverage_rows.append(cov)
            continue
        alignment_text = f"{raw_unit} -> {t_l} (x{factor * sign:g})"
        unit_alignment.setdefault(tkey, [])
        if alignment_text not in unit_alignment[tkey]:
            unit_alignment[tkey].append(alignment_text)
        extracted_source.setdefault(tkey, set()).add((coll, id_col))
        sub_value = sub_value * factor * sign
        if section_special_factor.get(tkey):
            cf_key = (fkey, coll)
            if cf_key not in child_factor_cache:
                child_codes, child_uniques = pd.factorize(part["Child Name"].astype(str))
                child_factors = np.array([contract_factor.get(normalize_text(s), 1.0) for s in child_uniques], dtype=float)
                child_factor_cache[cf_key] = pd.Series(child_factors[child_codes] if len(child_factors) else np.array([], dtype=float), index=part.index)
            cf_all = child_factor_cache[cf_key]
            sub_value = sub_value * (cf_all if sub_mask is None else cf_all[sub_mask])
        work = pd.DataFrame({"Report Key": key_series, "Month Label": sub["Month Label"], "Value": sub_value})
        pv_keys = ["Report Key", "Month Label"]
        pv_grouped = work.groupby(pv_keys)["Value"]
        pv_values = pv_grouped.mean() if use_mean else pv_grouped.sum(min_count=1)
        pv_multi_mask = (pv_grouped.transform("size") > 1).to_numpy()
        if pv_multi_mask.any():
            pv_multi = work[pv_multi_mask].groupby(pv_keys)["Value"].agg((lambda group_values: group_values.mean()) if use_mean else (lambda group_values: group_values.sum(min_count=1)))
            pv_values.loc[pv_multi.index] = pv_multi
        pv = pv_values.dropna().unstack("Month Label").reindex(columns=month_labels)
        disp = dedupe.drop_duplicates("k").set_index("k")["n"].to_dict()
        names = dedupe.groupby("k")["i"].agg(lambda s: " + ".join(sorted(set(str(x) for x in s)))).to_dict()
        if tkey in extracted:
            extracted[tkey] = extracted[tkey].add(pv, fill_value=0.0)
            extracted_display[tkey].update({k: v for k, v in disp.items() if k not in extracted_display[tkey]})
            for k, v in names.items():
                extracted_names[tkey][k] = (extracted_names[tkey][k] + " + " + v) if k in extracted_names[tkey] else v
        else:
            extracted[tkey] = pv
            extracted_display[tkey] = dict(disp)
            extracted_names[tkey] = names
            extracted_idonly[tkey] = set()
            extracted_rate[tkey] = use_mean
        cov["Status"] = "EXTRACTED" if not derived_components else "EXTRACTED (derived measure)"
        coverage_rows.append(cov)
    table_order.sort(key=section_sort_key)
    scope_missing_from_blueprint = [t for t in in_scope_tables if t not in table_order]
    print(f"  Scope: {len(in_scope_tables)} Standard sections in scope; {len(out_of_scope_tables)} Blueprint_std sections outside the scope were excluded")
    if scope_missing_from_blueprint:
        print(f"  WARNING: in-scope section(s) not found in Blueprint_std: {scope_missing_from_blueprint}")
    return extracted, extracted_display, extracted_names, extracted_idonly, extracted_rate, extracted_source, unit_alignment, pd.DataFrame(coverage_rows), table_order, out_of_scope_tables, blueprint_titles
def read_month_matrix(frame, month_labels, as_text):
    """The monthly columns of a section table as a float matrix (rows x months). A month column the table does not have stays NaN (reported as unable to evaluate). as_text=True: the cells are report text (remove "," "$" "%" -> number, unreadable = blank); False: numeric cells (unreadable = blank)."""
    matrix = np.full((len(frame), len(month_labels)), np.nan)
    positions = [i for i, month_name in enumerate(month_labels) if month_name in frame.columns]
    if len(frame) > 0 and len(positions) > 0:
        block = frame[[month_labels[i] for i in positions]]
        matrix[:, positions] = to_numeric_matrix(block) if as_text else block.apply(pd.to_numeric, errors="coerce").to_numpy(dtype=float)
    return matrix
def rebuild_table3_output_rows(px_df, px_matrix, table3_px_values):
    """Table 3 (Thermal Unit Fuel Use): the output side is rebuilt as (Primary) + (Secondary) + (Topping), the same definition as the raw Offtake: every output row (title + occurrence) with a rebuilt series takes it. Updates px_matrix in place."""
    occurrence_seen = {}
    for row_position, row_key in enumerate(px_df.iloc[:, 0].fillna("").astype(str).str.replace(r"\s+", " ", regex=True).str.strip().str.lower().tolist()):
        occurrence = occurrence_seen.get(row_key, 0)
        occurrence_seen[row_key] = occurrence + 1
        if row_key in table3_px_values and occurrence < len(table3_px_values[row_key]):
            px_matrix[row_position, :] = np.asarray(table3_px_values[row_key][occurrence], dtype=float)
def build_monthly_magnitude_rows(report_name, table_number, table_title, month_labels, raw_df, px_df, raw_matrix, px_matrix, unit_alignment_text, zero_threshold, sit_step):
    """The monthly table-sum comparison of ONE section: for every month the SUM of all resource values on the raw side and on the output side must share the same base-10 order of magnitude (the power of ten is read exactly from the decimal form of the sum; a zero sum only matches a zero sum). A blank value is nothing to add; a month with no numeric value on either side is NO DATA (not a failure); a missing month column is UNABLE TO EVALUATE (a failure). Returns the result rows and the counts {Months Checked, Months Failed, Months Unable, Months No Data}."""
    n_months = len(month_labels)
    raw_count_vec = np.sum(~np.isnan(raw_matrix), axis=0) if raw_matrix.shape[0] > 0 else np.zeros(n_months, dtype=int)
    px_count_vec = np.sum(~np.isnan(px_matrix), axis=0) if px_matrix.shape[0] > 0 else np.zeros(n_months, dtype=int)
    raw_sum_vec = np.nansum(raw_matrix, axis=0) if raw_matrix.shape[0] > 0 else np.zeros(n_months)
    px_sum_vec = np.nansum(px_matrix, axis=0) if px_matrix.shape[0] > 0 else np.zeros(n_months)
    raw_rows_summed = int((~np.isnan(raw_matrix)).any(axis=1).sum()) if raw_matrix.shape[0] > 0 else 0
    px_rows_summed = int((~np.isnan(px_matrix)).any(axis=1).sum()) if px_matrix.shape[0] > 0 else 0
    counts = {"Months Checked": 0, "Months Failed": 0, "Months Unable": 0, "Months No Data": 0}
    rows = []
    for month_index, month_name in enumerate(month_labels):
        raw_has_month, px_has_month = month_name in raw_df.columns, month_name in px_df.columns
        row_out = {"SIT Step": sit_step, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Period": month_name, "Raw Rows Summed": raw_rows_summed, "Output Rows Summed": px_rows_summed,
                   "Raw Sum": np.nan, "Output Sum": np.nan, "Raw Magnitude": "", "Output Magnitude": "", "Magnitude Difference (powers of ten)": "", "Output / Raw Ratio": np.nan, "Unit Alignment": unit_alignment_text,
                   "Magnitude Match": "", "Status": "", "Note": ""}
        if (not raw_has_month) or (not px_has_month):
            row_out["Status"] = "UNABLE TO EVALUATE"
            row_out["Note"] = "the month column is missing from the " + ("raw data" if not raw_has_month else "output")
            counts["Months Unable"] += 1
        elif raw_count_vec[month_index] == 0 and px_count_vec[month_index] == 0:
            row_out["Status"] = "NO DATA"
            row_out["Note"] = "no numeric value on either side for this month (not a failure)"
            counts["Months No Data"] += 1
        else:
            raw_sum_value, px_sum_value = float(raw_sum_vec[month_index]), float(px_sum_vec[month_index])
            raw_magnitude = "ZERO" if abs(raw_sum_value) < zero_threshold else Decimal(repr(float(abs(raw_sum_value)))).adjusted()
            px_magnitude = "ZERO" if abs(px_sum_value) < zero_threshold else Decimal(repr(float(abs(px_sum_value)))).adjusted()
            matched_magnitude = raw_magnitude == px_magnitude
            row_out.update({"Raw Sum": raw_sum_value, "Output Sum": px_sum_value, "Raw Magnitude": raw_magnitude, "Output Magnitude": px_magnitude, "Magnitude Match": int(matched_magnitude), "Status": "PASS" if matched_magnitude else "FAIL"})
            if isinstance(raw_magnitude, int) and isinstance(px_magnitude, int):
                row_out["Magnitude Difference (powers of ten)"] = px_magnitude - raw_magnitude
            if abs(raw_sum_value) >= zero_threshold:
                row_out["Output / Raw Ratio"] = px_sum_value / raw_sum_value
            if raw_count_vec[month_index] == 0:
                row_out["Note"] = "no raw value for this month: the raw sum is taken as 0"
            elif px_count_vec[month_index] == 0:
                row_out["Note"] = "no output value for this month: the output sum is taken as 0"
            if not matched_magnitude:
                counts["Months Failed"] += 1
        counts["Months Checked"] += 1 if row_out["Status"] in ("PASS", "FAIL") else 0
        rows.append(row_out)
    return rows, counts
def match_raw_identifiers(report_name, table_number, table_title, raw_titles, px_df, raw_name_lookup, source_text, sit_step):
    """Every raw identifier (the printed row title after the approved maptable_ normalization) must have a matching output row title: exact, or equal after a case-insensitive, whitespace-tolerant comparison. Returns the identifier rows, the section summary row and the (identifiers checked, mismatched) counts."""
    px_titles_exact = set(px_df.iloc[:, 0].fillna("").astype(str).str.strip().tolist()) if px_df.shape[1] > 0 else set()
    px_titles_norm = set(normalize_text(t) for t in px_titles_exact if t != "")
    raw_norm_set, identifier_rows = set(), []
    identifier_count = matched_count = mismatched_count = 0
    for raw_title in raw_titles:
        if raw_title == "":
            continue
        identifier_count += 1
        raw_key = normalize_text(raw_title)
        raw_norm_set.add(raw_key)
        raw_names_text = raw_name_lookup.get(raw_key, "")
        match_type = "Exact" if raw_title in px_titles_exact else ("Case / whitespace normalized" if raw_key in px_titles_norm else "No match")
        normalization = ""
        if raw_names_text != "":
            normalization = "none" if normalize_text(raw_names_text) == raw_key else "maptable_ rename (raw name -> printed row title)"
        matched = match_type != "No match"
        matched_count += 1 if matched else 0
        mismatched_count += 0 if matched else 1
        identifier_rows.append({"SIT Step": sit_step, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Identifier (row title)": raw_title, "Raw Data Name(s)": raw_names_text,
                                "Raw Identifier Source": source_text, "Approved Normalization": normalization, "Match Type": match_type, "Status": "PASS" if matched else "FAIL",
                                "Note": "" if matched else "no case-insensitive / whitespace-tolerant match among the output row titles of this section"})
    summary_row = {"SIT Step": sit_step, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Identifier Count": identifier_count, "Matched Count": matched_count, "Mismatched Count": mismatched_count,
                   "Output Identifiers Not In Raw (informational)": len(px_titles_norm - raw_norm_set), "Status": "PASS" if mismatched_count == 0 else "FAIL"}
    return identifier_rows, summary_row, identifier_count, mismatched_count
def compare_section_baseline(report_name, table_number, raw_entry, px_entry, month_labels, blueprint_titles, extracted_names, extracted_source, unit_alignment, cov_df, table3_px_values, no_counterpart, ratings_no_raw_reason, zero_threshold, sit_step):
    """The baseline comparison of ONE section (Standard section or rating period). Without a raw counterpart the section is listed as 'No solution.zip counterpart' (the reason comes from the Blueprint coverage table). A mapped section missing from the output: every month UNABLE TO EVALUATE and every raw identifier missing. Otherwise: the monthly table sums on both sides (Table 3 output = Primary + Secondary + Topping) must share the same order of magnitude and every raw identifier must have a matching output row title. Returns info (the section record used by the pass / fail summary), magnitude_rows, identifier_rows and identifier_summary_row (None when the section has no raw counterpart)."""
    raw_present, px_present = raw_entry is not None, px_entry is not None
    table_title = raw_entry["title"] if raw_present else (px_entry["title"] if px_present else blueprint_titles.get(table_number, ""))
    info = {"Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Present": raw_present, "PLEXOS Present": px_present,
            "Unit Alignment": "; ".join(unit_alignment.get(table_number, [])) if report_name == "Standard Report" else ("(rating raw data is already in report units)" if raw_present else ""),
            "Months Checked": 0, "Months Failed": 0, "Months Unable": 0, "Months No Data": 0, "Identifiers Checked": 0, "Identifiers Mismatched": 0, "Note": ""}
    if not raw_present:
        reasons = cov_df[(cov_df["Table"] == table_number) & (cov_df["Status"] != "DUPLICATE BLUEPRINT ROW - ignored")] if (report_name == "Standard Report" and "Table" in cov_df.columns) else pd.DataFrame()
        if report_name == "Ratings Report":
            info["Note"] = ratings_no_raw_reason
        elif len(reasons) > 0:
            info["Note"] = "; ".join(sorted(set(reasons["Status"] + ": " + reasons["Note"])))
        else:
            info["Note"] = "Section has no raw counterpart (no raw measure for it in the raw data)"
        if not px_present and report_name == "Standard Report":
            info["Note"] += "; the section is not in the output either"
        info["Section Status"] = "N/A - " + no_counterpart
        return info, [], [], None
    raw_df = raw_entry["data"]
    raw_name_lookup = extracted_names.get(table_number, {}) if report_name == "Standard Report" else {}
    source_text = ", ".join(sorted(f"{coll}.{col}" for coll, col in extracted_source.get(table_number, set()))) if report_name == "Standard Report" else "Child Name"
    raw_titles = raw_df.iloc[:, 0].fillna("").astype(str).str.strip().tolist() if raw_df.shape[1] > 0 else []
    if not px_present:
        magnitude_rows = [{"SIT Step": sit_step, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Period": month_name, "Raw Rows Summed": np.nan, "Output Rows Summed": 0, "Raw Sum": np.nan,
                           "Output Sum": np.nan, "Raw Magnitude": "", "Output Magnitude": "", "Magnitude Difference (powers of ten)": "", "Output / Raw Ratio": np.nan, "Unit Alignment": info["Unit Alignment"], "Magnitude Match": "",
                           "Status": "UNABLE TO EVALUATE", "Note": "mapped section is missing from the output"} for month_name in month_labels]
        identifier_rows = [{"SIT Step": sit_step, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Identifier (row title)": raw_title, "Raw Data Name(s)": raw_name_lookup.get(normalize_text(raw_title), ""),
                            "Raw Identifier Source": source_text, "Approved Normalization": "", "Match Type": "No match", "Status": "FAIL", "Note": "the mapped section is missing from the output"} for raw_title in raw_titles if raw_title != ""]
        info["Months Unable"], info["Identifiers Checked"], info["Identifiers Mismatched"] = len(month_labels), len(identifier_rows), len(identifier_rows)
        info["Note"] = "mapped section is missing from the output"
        return info, magnitude_rows, identifier_rows, {"SIT Step": sit_step, "Report": report_name, "Table Number": table_number, "Table Title": table_title, "Raw Identifier Count": len(identifier_rows), "Matched Count": 0,
                                                       "Mismatched Count": len(identifier_rows), "Output Identifiers Not In Raw (informational)": 0, "Status": "FAIL"}
    px_df = px_entry["data"]
    raw_matrix, px_matrix = read_month_matrix(raw_df, month_labels, False), read_month_matrix(px_df, month_labels, True)
    if report_name == "Standard Report" and table_number == "3" and len(table3_px_values) > 0:
        rebuild_table3_output_rows(px_df, px_matrix, table3_px_values)
    magnitude_rows, counts = build_monthly_magnitude_rows(report_name, table_number, table_title, month_labels, raw_df, px_df, raw_matrix, px_matrix, info["Unit Alignment"], zero_threshold, sit_step)
    info.update(counts)
    identifier_rows, identifier_summary_row, info["Identifiers Checked"], info["Identifiers Mismatched"] = match_raw_identifiers(report_name, table_number, table_title, raw_titles, px_df, raw_name_lookup, source_text, sit_step)
    raw_months_present, px_months_present = len([m for m in month_labels if m in raw_df.columns]), len([m for m in month_labels if m in px_df.columns])
    info["Note"] = f"month columns present: raw {raw_months_present}, output {px_months_present} of {len(month_labels)}" if (raw_months_present != len(month_labels) or px_months_present != len(month_labels)) else ""
    return info, magnitude_rows, identifier_rows, identifier_summary_row
def print_grouped_failures(failures, group_columns, count_name, line_formatter, more_text, max_lines=15):
    """Print the failing rows of a step: the count per group (report / section), the first max_lines rows through line_formatter and '... and N more (more_text)'. Prints nothing when there are no failures."""
    if failures.empty:
        return
    print(failures.groupby(group_columns).size().reset_index(name=count_name).to_string(index=False))
    for _, failure in failures.head(max_lines).iterrows():
        print(f"    {line_formatter(failure)}")
    if len(failures) > max_lines:
        print(f"    ... and {len(failures) - max_lines} more ({more_text})")
def recheck_magnitude_labels(magnitude_checked, zero_threshold):
    """Step 4: every monthly table sum is recomputed independently with the log10 method (the engine reads the power of ten exactly from the decimal form): the recomputed mismatch must be labeled FAIL and a match must not be. A sum that is an exact power of ten is decided by the decimal method only (the log10 method cannot be trusted there) and is counted as a boundary value. Returns independent_mismatches, boundary_cases and label_errors ((report, table, period) whose label disagrees)."""
    independent_mismatches, boundary_cases, label_errors = 0, 0, []
    for check_report, check_table, check_period, check_status, check_raw, check_px in zip(magnitude_checked["Report"].tolist(), magnitude_checked["Table Number"].tolist(), magnitude_checked["Period"].tolist(),
                                                                                            magnitude_checked["Status"].tolist(), magnitude_checked["Raw Sum"].tolist(), magnitude_checked["Output Sum"].tolist()):
        raw_value, px_value = float(check_raw), float(check_px)
        raw_log = None if abs(raw_value) < zero_threshold else math.log10(abs(raw_value))
        px_log = None if abs(px_value) < zero_threshold else math.log10(abs(px_value))
        near_boundary = (raw_log is not None and abs(raw_log - round(raw_log)) < 1e-9) or (px_log is not None and abs(px_log - round(px_log)) < 1e-9)
        independent_differs = ("ZERO" if raw_log is None else math.floor(raw_log)) != ("ZERO" if px_log is None else math.floor(px_log))
        if near_boundary:
            boundary_cases += 1
            continue
        independent_mismatches += 1 if independent_differs else 0
        if independent_differs != (check_status == "FAIL"):
            label_errors.append((check_report, check_table, check_period))
    return independent_mismatches, boundary_cases, label_errors
def write_validation_exports(exports, results_folder, numeric_columns, status_text):
    """Step 5: write every validation report (the numeric columns rounded to 5 decimals), read it back and check the file exists, the row count and the required columns. exports = {label: (file name, table, required columns)}. Prints one line per file. Returns {label: bool}."""
    step_checks = {}
    for export_label, (file_name, export_frame, required_columns) in exports.items():
        export_copy = export_frame.copy()
        for numeric_column in numeric_columns:
            if numeric_column in export_copy.columns:
                export_copy[numeric_column] = pd.to_numeric(export_copy[numeric_column], errors="coerce").round(globals().get("OUTPUT_DECIMALS", 5))
        export_path = save_results_csv(export_copy, results_folder, file_name)
        file_ok = export_path.is_file()
        rows_ok = columns_ok = False
        if file_ok:
            try:
                readback = pd.read_csv(export_path)
            except pd.errors.EmptyDataError:
                readback = pd.DataFrame()
            rows_ok = len(readback) == len(export_frame)
            columns_ok = all(c in readback.columns for c in required_columns) if len(readback.columns) > 0 else False
        step_checks[export_label] = file_ok and rows_ok and columns_ok
        print(f"  {export_label}: {file_name} ({len(export_frame)} row(s)) -- written, row count and columns verified: {status_text[step_checks[export_label]]}")
    return step_checks
def reconcile_rating_periods(rating_px_tables, month_labels, rating_required_keys, zero_threshold, rating_moe, sit_step):
    """Rating dataset only: Off-Peak + On-Peak = ATC within the margin of error for every row / month. Rows are matched on the row title and occurrence across the three rating periods (the Sunday period is not part of it); a row or value missing from any of the three periods, or a missing section, is UNABLE TO EVALUATE (a failure). Returns rating_results, rating_skipped_reason (None when it ran) and rating_months_used."""
    rating_columns = ["SIT Step", "Row Title", "Occurrence", "Period", "Off-Peak Value", "On-Peak Value", "Computed Sum (Off-Peak + On-Peak)", "ATC Value", "Difference", "Percent Difference", "Within 1% MOE", "Status", "Note"]
    rating_missing_keys = [k for k in rating_required_keys if k not in rating_px_tables]
    if len(rating_missing_keys) > 0:
        return pd.DataFrame([], columns=rating_columns), f"required rating-period section(s) missing from the Rating dataset: {rating_missing_keys}", []
    prepared = {}
    for rating_key in rating_required_keys:
        rating_frame = rating_px_tables[rating_key]["data"].copy()
        rating_frame.columns = rating_frame.columns.astype(str).str.strip()
        rating_frame = rating_frame.rename(columns={rating_frame.columns[0]: "Row Title"})
        rating_frame["Row Title"] = rating_frame["Row Title"].fillna("").astype(str).str.strip()
        rating_frame["Row Key"] = rating_frame["Row Title"].str.replace(r"\s+", " ", regex=True).str.lower()
        rating_frame = rating_frame[rating_frame["Row Key"] != ""].copy()
        rating_frame["Occurrence"] = rating_frame.groupby("Row Key").cumcount() + 1
        prepared[rating_key] = rating_frame
    rating_months_used = [m for m in month_labels if all(m in prepared[k].columns for k in rating_required_keys)]
    if len(rating_months_used) == 0:
        return pd.DataFrame([], columns=rating_columns), "no monthly column is shared by the Off-Peak, On-Peak and ATC rating periods", rating_months_used
    long_frames = {}
    value_names = {"atc": "ATC Value", "offpeak": "Off-Peak Value", "onpeak": "On-Peak Value"}
    for rating_key in rating_required_keys:
        frame = prepared[rating_key]
        if frame.columns.is_unique:
            frame[rating_months_used] = pd.DataFrame(to_numeric_matrix(frame[rating_months_used]), index=frame.index, columns=rating_months_used)
        else:
            for month_name in rating_months_used:
                frame[month_name] = pd.to_numeric(frame[month_name].astype(str).str.replace(",", "", regex=False).str.replace("$", "", regex=False).str.replace("%", "", regex=False), errors="coerce")
        long_frames[rating_key] = frame.melt(id_vars=["Row Key", "Row Title", "Occurrence"], value_vars=rating_months_used, var_name="Period", value_name=value_names[rating_key])
    merged = long_frames["atc"][["Row Key", "Row Title", "Occurrence", "Period", "ATC Value"]].merge(long_frames["offpeak"][["Row Key", "Occurrence", "Period", "Off-Peak Value"]], on=["Row Key", "Occurrence", "Period"], how="outer", indicator="offpeak_join")
    merged = merged.merge(long_frames["onpeak"][["Row Key", "Occurrence", "Period", "On-Peak Value"]], on=["Row Key", "Occurrence", "Period"], how="outer", indicator="onpeak_join")
    merged["Row Title"] = merged["Row Title"].fillna(merged["Row Key"])
    merged["Computed Sum (Off-Peak + On-Peak)"] = merged["Off-Peak Value"] + merged["On-Peak Value"]
    merged["Difference"] = merged["Computed Sum (Off-Peak + On-Peak)"] - merged["ATC Value"]
    unable_mask = merged["ATC Value"].isna() | merged["Off-Peak Value"].isna() | merged["On-Peak Value"].isna()
    percent = pd.Series(np.nan, index=merged.index)
    evaluable = ~unable_mask
    atc_zero = evaluable & (merged["ATC Value"].abs() < zero_threshold)
    atc_nonzero = evaluable & ~atc_zero
    sum_zero = merged["Computed Sum (Off-Peak + On-Peak)"].abs() < zero_threshold
    percent.loc[atc_zero & sum_zero] = 0.0
    percent.loc[atc_zero & ~sum_zero] = np.inf
    percent.loc[atc_nonzero] = merged.loc[atc_nonzero, "Difference"].abs() / merged.loc[atc_nonzero, "ATC Value"].abs()
    merged["Percent Difference"] = percent
    merged["Within 1% MOE"] = (evaluable & (percent <= rating_moe)).astype(int)
    merged["Status"] = np.where(unable_mask, "UNABLE TO EVALUATE", np.where(merged["Within 1% MOE"] == 1, "PASS", "FAIL"))
    merged["Note"] = ["; ".join(piece for piece, is_missing in (("no ATC value", a), ("no Off-Peak value", o), ("no On-Peak value", n)) if is_missing) for a, o, n in zip(merged["ATC Value"].isna().tolist(), merged["Off-Peak Value"].isna().tolist(), merged["On-Peak Value"].isna().tolist())]
    merged["SIT Step"] = sit_step
    return pd.DataFrame(merged[rating_columns].to_dict("records"), columns=rating_columns), None, rating_months_used
def build_section_summary(section_info, rating_results, rating_skipped_reason, rating_required_keys, no_counterpart):
    """Step 6: the pass / fail summary of every Standard section and rating period: FAIL when a mapped section is missing from the output, a month failed or could not be evaluated or a raw identifier has no match; a section without a raw counterpart shows 'No solution.zip counterpart'; every rating period shows the Off-Peak + On-Peak = ATC reconciliation result."""
    rating_failures, rating_unable = rating_results[rating_results["Status"] == "FAIL"], rating_results[rating_results["Status"] == "UNABLE TO EVALUATE"]
    summary_rows = []
    for (report_label, table_label), info in section_info.items():
        if info["Raw Present"]:
            section_status = "FAIL" if ((not info["PLEXOS Present"]) or info["Months Failed"] > 0 or info["Months Unable"] > 0 or info["Identifiers Mismatched"] > 0) else "PASS"
        else:
            section_status = "N/A - " + no_counterpart
        reconciliation_status = ""
        if report_label == "Ratings Report":
            if rating_skipped_reason is not None:
                reconciliation_status = "FAIL (could not be evaluated)"
            elif table_label in rating_required_keys:
                reconciliation_status = "FAIL" if (len(rating_failures) > 0 or len(rating_unable) > 0) else "PASS"
            else:
                reconciliation_status = "N/A (not part of the Off-Peak + On-Peak = ATC reconciliation)"
        summary_rows.append({"Report": report_label, "Table Number": table_label, "Table Title": info["Table Title"], "Section Status": section_status, "Months Checked": info["Months Checked"], "Months Failed": info["Months Failed"],
                             "Months Unable To Evaluate": info["Months Unable"], "Months With No Data": info["Months No Data"], "Raw Identifiers Checked": info["Identifiers Checked"], "Raw Identifiers Without A Match": info["Identifiers Mismatched"],
                             "Unit Alignment": info["Unit Alignment"], "Rating Reconciliation (Off-Peak + On-Peak = ATC)": reconciliation_status, "Note": info["Note"]})
    return pd.DataFrame(summary_rows)
def verify_section_summary(summary_path, n_standard, n_rating, n_sections, in_scope_tables, no_counterpart):
    """Step 6: the written summary is read back and checked: file written, one row per Standard section and rating period, every Standard section in scope listed, every row has a PASS / FAIL / 'No solution.zip counterpart' status, both datasets present, and every section without a raw counterpart labeled as such. Returns {check label: bool}."""
    labels = (f"One row per Standard section and Rating period ({{}} row(s); {n_standard} Standard + {n_rating} rating)", "Every Standard section in scope is listed", f"Every section has a PASS / FAIL / '{no_counterpart}' status",
              "Both datasets are present (Standard and Ratings)", f"Sections without a raw counterpart are labeled '{no_counterpart}'")
    checks = {"Section summary written": summary_path.is_file()}
    if summary_path.is_file():
        readback = pd.read_csv(summary_path)
        standard_in_summary = set(readback[readback["Report"] == "Standard Report"]["Table Number"].astype(str))
        unmapped_labeled = readback[~readback["Section Status"].astype(str).str.match(r"^(PASS|FAIL)$")]
        checks[labels[0].format(len(readback))] = len(readback) == n_standard + n_rating == n_sections
        checks[labels[1]] = all(t in standard_in_summary for t in in_scope_tables)
        checks[labels[2]] = bool(readback["Section Status"].astype(str).str.match(r"^(PASS|FAIL|N/A - " + re.escape(no_counterpart) + r")$").all())
        checks[labels[3]] = set(readback["Report"]) == {"Standard Report", "Ratings Report"}
        checks[labels[4]] = bool(unmapped_labeled["Section Status"].astype(str).str.contains(no_counterpart).all())
    else:
        for label in labels:
            checks[label.format(0)] = False
    return checks
def write_rating_reconciliation_files(rating_results, results_folder):
    """Step 7: write the rating reconciliation (every row / month, numbers rounded to 5 decimals), its exceptions (FAIL and UNABLE TO EVALUATE) and the per-row summary, and read the main file back. Returns rating_output_path, rating_exception_frame, by_row, files_ok, rows_ok."""
    rating_export = rating_results.copy()
    for numeric_column in ["Off-Peak Value", "On-Peak Value", "Computed Sum (Off-Peak + On-Peak)", "ATC Value", "Difference", "Percent Difference"]:
        rating_export[numeric_column] = pd.to_numeric(rating_export[numeric_column], errors="coerce").round(globals().get("OUTPUT_DECIMALS", 5))
    rating_output_path = save_results_csv(rating_export, results_folder, "PlexOS_3_07_Ratings_Period_Correlation.csv")
    rating_exception_frame = rating_export[rating_export["Status"].isin(["FAIL", "UNABLE TO EVALUATE"])]
    rating_exceptions_path = save_results_csv(rating_exception_frame, results_folder, "PlexOS_3_07_Ratings_Period_Correlation_Exceptions.csv")
    if not rating_results.empty:
        by_row = rating_results.groupby(["Row Title"]).agg(Months_Checked=("Status", "size"), Months_Passed=("Status", lambda s: int((s == "PASS").sum())), Months_Failed=("Status", lambda s: int((s == "FAIL").sum())),
                                                           Months_Unable=("Status", lambda s: int((s == "UNABLE TO EVALUATE").sum())), Max_Percent_Difference=("Percent Difference", "max")).reset_index()
        by_row["Max_Percent_Difference"] = by_row["Max_Percent_Difference"].round(globals().get("OUTPUT_DECIMALS", 5))
    else:
        by_row = pd.DataFrame(columns=["Row Title", "Months_Checked", "Months_Passed", "Months_Failed", "Months_Unable", "Max_Percent_Difference"])
    rating_row_summary_path = save_results_csv(by_row, results_folder, "PlexOS_3_07_Ratings_Period_Correlation_By_Row.csv")
    files_ok = rating_output_path.is_file() and rating_exceptions_path.is_file() and rating_row_summary_path.is_file()
    rows_ok = len(pd.read_csv(rating_output_path)) == len(rating_results) if rating_output_path.is_file() else False
    return rating_output_path, rating_exception_frame, by_row, files_ok, rows_ok

################################################################################################################################################################################
#3.08
################################################################################################################################################################################
def show_frame(frame):
    """Show a table with the notebook's display() (IPython's display when the namespace has none; printed as text without IPython)."""
    try:
        display_function = display
    except NameError:
        try:
            from IPython.display import display as display_function
        except ImportError:
            display_function = lambda shown_frame: print(shown_frame.to_string())
    display_function(frame)
def session_has_format_issues():
    """True when this session holds a `reports` object whose every report has the format issues stored by the report parser of an earlier test (reports[...]['PLEXOS_format_issues'])."""
    session_reports = globals().get("reports")
    return bool(session_reports is not None and len(session_reports) > 0 and all(("PLEXOS_format_issues" in report_cfg) for report_cfg in session_reports.values()))
def find_malformed_rows(report_rows, is_standard_report):
    """One pass over the rows of a PLEXOS report keeping only the row lengths. A section starts at a header row (Standard: '(n) title'; Ratings: a row with exactly one non-blank cell); the first non-empty row of a section is its column-header row (a section split into several chunks keeps the header of its first chunk) and every later non-empty row whose number of cells differs from it is malformed. Same rule as parse_plexos_report_sections, without building the section tables. Returns a table with Table Number, Table Title, Expected Columns, Actual Columns (empty when nothing is malformed)."""
    standard_header_re = re.compile(r"^\(\s*(\d+[a-zA-Z]?)\s*\)")
    header_lengths, scan_issues = {}, []
    current_section, current_title, current_row_lengths = None, None, []
    for row in chain(report_rows, (None,)):
        if row is None:
            is_header_row, header_match = True, None
        else:
            non_blank = [cell_text for cell_text in (str(cell).strip() for cell in row) if cell_text]
            row_text = " ".join(non_blank)
            if is_standard_report:
                header_match = standard_header_re.match(row_text)
                is_header_row = header_match is not None
            else:
                is_header_row = len(non_blank) == 1
        if is_header_row:
            if current_section is not None and len(current_row_lengths) > 0:
                if current_section in header_lengths:
                    header_length, data_row_lengths = header_lengths[current_section], current_row_lengths
                else:
                    header_length = header_lengths[current_section] = current_row_lengths[0]
                    data_row_lengths = current_row_lengths[1:]
                for data_row_length in data_row_lengths:
                    if data_row_length != header_length:
                        scan_issues.append({"Table Number": current_section, "Table Title": current_title, "Expected Columns": header_length, "Actual Columns": data_row_length})
            if row is None:
                break
            current_section = header_match.group(1).lower() if is_standard_report else canonicalize_ratings_section_title(row_text)
            current_title, current_row_lengths = row_text, []
        elif current_section is not None and len(non_blank) > 0:
            current_row_lengths.append(len(row))
    return pd.DataFrame(scan_issues)
def scan_report_files_for_format_issues(report_paths):
    """The session does not hold the format issues: scan the report files directly (report_paths = [(report name, csv path), ...]). Prints one line saying so. Returns {report name: {"PLEXOS_format_issues": malformed rows}} (never replaces an existing `reports` object)."""
    scanned = {}
    for report_name, report_path in report_paths:
        with open(report_path, "r", encoding="utf-8-sig", errors="replace") as file:
            report_rows = list(csv.reader(file))
        scanned[report_name] = {"PLEXOS_format_issues": find_malformed_rows(report_rows, report_name == "Standard Report")}
    print(f"(PlexOS-3.08: the format issues were not in this session, so the Standard and Ratings report files from the SIT Inputs block were scanned directly: "
          f"{sum(len(cfg['PLEXOS_format_issues']) for cfg in scanned.values())} malformed row(s) found)")
    return scanned
def label_format_issues(issues, sit_step, report_name, version):
    """A copy of a report's malformed-row table with the SIT Step, Report, Version and Status (always FAIL) columns added; an empty table stays empty."""
    labeled = issues.copy()
    if not labeled.empty:
        labeled["SIT Step"], labeled["Report"], labeled["Version"], labeled["Status"] = sit_step, report_name, version, "FAIL"
    return labeled
def build_format_exceptions(format_source_reports, sit_step):
    """Every malformed row of every report (RT_Sim_format_issues, when present, and PLEXOS_format_issues), each a FAIL. Also stored on every report as report_config["format_exceptions"] so PlexOS-3.09 / 3.10 can read the report's count without recomputing it. Returns format_exceptions (one table, empty with the SIT Step / Report / Version / Status columns when nothing is malformed)."""
    all_format_exceptions = []
    for report_name, report_config in format_source_reports.items():
        labeled_issues = [label_format_issues(report_config.get(issue_key, pd.DataFrame()), sit_step, report_name, version) for issue_key, version in (("RT_Sim_format_issues", "RT_Sim"), ("PLEXOS_format_issues", "PLEXOS"))]
        labeled_issues = [labeled for labeled in labeled_issues if not labeled.empty]
        all_format_exceptions.extend(labeled_issues)
        report_config["format_exceptions"] = pd.concat(labeled_issues, ignore_index=True) if labeled_issues else pd.DataFrame()
    return pd.concat(all_format_exceptions, ignore_index=True) if len(all_format_exceptions) > 0 else pd.DataFrame(columns=["SIT Step", "Report", "Version", "Status"])
def keep_format_exceptions_for_later_tests(format_source_reports):
    """The results came from a direct scan: keep them in format_check_reports (for PlexOS-3.09 / 3.10) and, when the session has a `reports` object, on its matching reports as well. An existing `reports` object is never replaced."""
    globals()["format_check_reports"] = format_source_reports
    session_reports = globals().get("reports")
    if session_reports is not None:
        for report_name, report_config in format_source_reports.items():
            if report_name in session_reports:
                session_reports[report_name]["format_exceptions"] = report_config["format_exceptions"]
def print_format_exception_results(format_exceptions, report_names, sit_step):
    """The PASS / FAIL line of the test and, for every report, its number of format exceptions and the exception rows."""
    if len(format_exceptions) == 0:
        print(f"{sit_step} PASS: No malformed rows identified.")
    else:
        print(f"{sit_step} FAIL: {len(format_exceptions)} malformed rows identified.")
        show_frame(format_exceptions)
    for report_name in report_names:
        report_exceptions = format_exceptions[format_exceptions["Report"] == report_name] if not format_exceptions.empty else format_exceptions
        print(report_name)
        print(f"Format Exceptions: {len(report_exceptions)}")
        if len(report_exceptions) > 0:
            show_frame(report_exceptions)
################################################################################################################################################################################
#3.09 & 3.10
################################################################################################################################################################################
def get_current_user_name():
    """Return the logged-in user name (getpass, else the USERNAME / USER environment variable, else '')."""
    try:
        return __import__("getpass").getuser()
    except Exception:
        return os.environ.get("USERNAME", "") or os.environ.get("USER", "")
def get_host_and_platform():
    """Return (host name, platform text) of the machine running the notebook; '' / os.name when they cannot be read."""
    try:
        host_name = __import__("socket").gethostname()
    except Exception:
        host_name = os.environ.get("COMPUTERNAME", "")
    try:
        platform_text = __import__("platform").platform()
    except Exception:
        platform_text = os.name
    return host_name, platform_text
def hash_file_sha256(file_path, chunk_size=1 << 20):
    """SHA-256 (hex) of a file, read in chunks."""
    digest = hashlib.sha256()
    with open(file_path, "rb") as handle:
        while True:
            block = handle.read(chunk_size)
            if not block:
                break
            digest.update(block)
    return digest.hexdigest()
def write_json_file(file_path, payload):
    """Write the payload as indented UTF-8 JSON (values JSON cannot store, such as numpy numbers or dates, are written as text) and return the path. REPLACES the 3.09 version, which had no default=str."""
    file_path = Path(file_path)
    file_path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
    return file_path


################################################################################################################################################################################
#4.00 PREPROCESSING
################################################################################################################################################################################
def read_oprep_requirements(workbook_path):
    """Read from an OpRep_01 workbook what its macros and lookup tabs need (the workbook is only read): the number of effluent types (Control), the columns the MISSING INDEX CHECK counts, every lookup formula of the checked tabs that searches a KeyedData column (XMATCH, also when it points to another workbook: [1]KeyedData) together with the text it looks up, and the RUIndex roll-up table. Returns a dict: effluents_count, check_sheets (sheet -> counted column pairs), lookups [(sheet, column, row, text, KeyedData column)], external_lookups (sheet -> number of lookups that point to ANOTHER workbook), ru_rows [(key, SecRollUpGWh, PlantRollUpGWh, SecRollUp$000)]."""
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=False)
    requirements = {"effluents_count": 8, "check_sheets": OrderedDict(), "lookups": [], "ru_rows": [], "external_lookups": Counter()}
    for row in workbook["Control"].iter_rows(min_row=1, max_row=60, max_col=11, values_only=True):
        if isinstance(row[1], str) and "number of effluent types" in row[1].lower() and isinstance(row[2], (int, float)):
            requirements["effluents_count"] = int(row[2])
        if isinstance(row[8], str) and "COUNTIFS" in row[8].upper():
            for sheet_name, first_column, last_column in re.findall(r"COUNTIFS\(\s*'?([^'!()]+)'?!\$?([A-Z]+):\$?([A-Z]+)\s*,\s*\"#N/A\"", row[8], flags=re.I):
                requirements["check_sheets"].setdefault(sheet_name, []).append((first_column.upper(), last_column.upper()))
    lookup_pattern = re.compile(r"XMATCH\(\s*\$?([A-Z]+)\$?(\d+)\s*,\s*(\[\d+\])?KeyedData!\$?([A-Z]+):\$?[A-Z]+\s*\)", re.I)
    for sheet_name, column_pairs in requirements["check_sheets"].items():
        if sheet_name not in workbook.sheetnames:
            continue
        counted = [column for first_column, last_column in column_pairs if column_index_from_string(last_column) <= 6 for column in get_column_letter_range(first_column, last_column)]
        if len(counted) == 0:
            continue
        sheet_rows = [list(r) for r in workbook[sheet_name].iter_rows(min_row=1, max_row=workbook[sheet_name].max_row, max_col=6, values_only=True)]
        for row_number, cells in enumerate(sheet_rows, start=1):
            for column in counted:
                formula = cells[column_index_from_string(column) - 1] if column_index_from_string(column) <= len(cells) else None
                found = lookup_pattern.search(formula) if isinstance(formula, str) else None
                if found is None:
                    continue
                if found.group(3):
                    requirements["external_lookups"][sheet_name] += 1
                text = sheet_rows[int(found.group(2)) - 1][column_index_from_string(found.group(1)) - 1]
                if text not in (None, ""):
                    requirements["lookups"].append((sheet_name, column, row_number, str(text), found.group(4).upper()))
    if "RUIndex" in workbook.sheetnames:
        requirements["ru_rows"] = [(str(r[1]), r[2], r[3], r[4]) for r in workbook["RUIndex"].iter_rows(min_row=2, max_row=workbook["RUIndex"].max_row, max_col=5, values_only=True) if r[1] not in (None, "")]
    workbook.close()
    return requirements
def get_column_letter_range(first_column, last_column):
    """Column letters from first_column to last_column (for example 'B' to 'D' -> ['B', 'C', 'D'])."""
    return [get_column_letter(number) for number in range(column_index_from_string(first_column), column_index_from_string(last_column) + 1)]
def read_keyed_data_reference(workbook_path):
    """The first four columns (ReportName, Account Name, PrimaryKey, Row) of the KeyedData tab of a workbook, for every row that has a key."""
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=True)
    reference = [tuple(r) for r in workbook["KeyedData"].iter_rows(min_row=2, max_row=workbook["KeyedData"].max_row, max_col=4, values_only=True) if r[2] not in (None, "")]
    workbook.close()
    return reference
def excel_cell_text(text):
    """What VBA reads from a CSV field after Excel opened it: a plain number loses its formatting ('01' -> '1'), everything else stays text."""
    if re.fullmatch(r"[-+]?\d+(\.\d+)?", text):
        number = float(text)
        return str(int(number)) if number.is_integer() else repr(number)
    return text
def format_macro_title(title_text):
    """' ( 1) System Summary' form of a Standard table title: one leading space so that '(' is the 2nd character (CreateStandardKeys only recognises a title then) and the section number right-aligned to 2 characters, as RT Sim writes it. Returns None when the text is not a table title (the '(1) Change Case File = ...' lines contain '=')."""
    found = re.match(r"^\s*\(\s*(\d+[a-z]?)\s*\)\s*(.*)$", title_text, flags=re.I)
    return None if (found is None or "=" in title_text) else " (" + found.group(1).rjust(2) + ") " + found.group(2)
def format_macro_month_cell(text):
    """Month header cell as RT Sim writes it: ' Jan-2026 ' (4-digit year, one space each side, so Excel keeps it as text and Control!F10 can read the year from the last 4 characters), ' Tot-2026 ', '    Total '. Any other text is returned unchanged."""
    found = re.fullmatch(r"\s*(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec|Tot)[-\s]?(\d{2}|\d{4})\s*", text, flags=re.I)
    if found:
        return " " + found.group(1).capitalize() + "-" + ("20" + found.group(2) if len(found.group(2)) == 2 else found.group(2)) + " "
    return "    Total " if text.strip().lower() == "total" else text
def macro_rating_section_name(text, rules):
    """The Ratings section name the macro recognises (exact spelling) for a section name of the report, by the first rule (letters / digits prefix, macro name) that fits; None when no rule fits."""
    key = re.sub(r"[^a-z0-9]", "", text.lower())
    return next((name for prefix, name in rules if key.startswith(prefix)), None)
def find_report_titles(rows, is_ratings):
    """Line indexes (0-based) of the table titles (Standard) or section titles (Ratings: one-cell line directly above a month-header row), in file order."""
    month_pattern = re.compile(r"^\s*(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec|Tot)[-\s]?\d{2,4}\s*$", re.I)
    header_positions = [month_header_position(cells, month_pattern) for cells in rows]
    titles = []
    for index, cells in enumerate(rows):
        if len([c for c in cells if c.strip() != ""]) == 1 and len(cells) > 0 and cells[0].strip() != "":
            if (is_ratings and index + 1 < len(rows) and header_positions[index + 1] is not None) or ((not is_ratings) and format_macro_title(cells[0]) is not None):
                titles.append(index)
    return titles, header_positions
def make_macro_ready_rows(rows, is_ratings, first_title_row, rating_rules):
    """Make a Standard or Ratings report readable for the OpRep_01 macros without touching a number: blank lines so that the first title is on first_title_row (the macros read from row 26 and Control takes the start year from B28), Standard titles as ' ( 1) Title', Ratings section names as the macro spells them, month headers as padded text. Returns (new rows, changes [(kind, original line, old text, new text)], layout note)."""
    rows = [list(cells) for cells in rows]
    titles, header_positions = find_report_titles(rows, is_ratings)
    changes = []
    layout_note = ""
    if len(titles) > 0:
        shift = first_title_row - (titles[0] + 1)
        if shift > 0:
            rows = [[] for _ in range(shift)] + rows
            header_positions = [None] * shift + header_positions
            titles = [t + shift for t in titles]
            changes.append(("blank lines added at the top", 0, "", str(shift)))
        elif shift < 0 and count_leading_blank_rows(rows) >= -shift:
            rows = rows[-shift:]
            header_positions = header_positions[-shift:]
            titles = [t + shift for t in titles]
            changes.append(("blank lines removed from the top", 0, str(-shift), ""))
        elif shift < 0:
            layout_note = f"the first title is on line {titles[0] + 1}, below row {first_title_row}, and the lines above it are not blank: nothing was removed"
    for index in titles:
        old = rows[index][0]
        new = (" " + macro_rating_section_name(old, rating_rules)) if (is_ratings and macro_rating_section_name(old, rating_rules) is not None) else (old if is_ratings else format_macro_title(old))
        if new != old:
            rows[index][0] = new
            changes.append(("section name" if is_ratings else "table title", index + 1, old, new))
    for index, offset in enumerate(header_positions):
        if offset is not None:
            changed_cells = 0
            for position in range(offset, len(rows[index])):
                new = format_macro_month_cell(rows[index][position])
                if new != rows[index][position]:
                    rows[index][position] = new
                    changed_cells += 1
            if changed_cells > 0:
                changes.append(("month header cells", index + 1, "", f"{changed_cells} cells"))
    return rows, changes, layout_note
def simulate_macro_keys(rows, is_ratings, effluents_count, first_row=26):
    """What CreateKeys.CreateStandardKeys / CreateRatingKeys of OpRep_01 writes into KeyedData columns A-D for a report file, row by row exactly as the macro reads it (column A only, from row 26 to the last used row). Returns (keys [(ReportName, Account Name, PrimaryKey, Row)], error text or '')."""
    last_row = len(rows)
    while last_row > 0 and all(c == "" for c in rows[last_row - 1]):
        last_row -= 1
    column_a = [excel_cell_text(cells[0]) if len(cells) > 0 else "" for cells in rows[:last_row]]
    trim = lambda text: text.strip(" ")
    keys = []
    report_name, section, plant, suffix = "", "", "", ""
    row = first_row
    while row <= last_row:
        label = column_a[row - 1]
        if trim(label) != "":
            if is_ratings:
                if trim(label) in ("On-peak Mon-Sat", "Off-peak 23-6 Mon-Sun", "Sunday On-peak", "ATC Mon-Sun"):
                    report_name = trim(label)
                else:
                    keys.append(("Rating Report", trim(label), "Rat_" + report_name + "_" + trim(label), row))
            elif label.find("(") + 1 == 2:
                if label.find(")", 1) < 0:
                    return keys, f"row {row}: the table title has no ')': the macro stops with a run-time error"
                section = trim(label[2:label.find(")", 1)])
                report_name = trim(label)
            else:
                if section in ("3", "6"):
                    if trim(label[:5]) == "":
                        suffix = "_" + trim(label)
                        record = "Std_" + section + plant + suffix
                    else:
                        plant = "_" + trim(label)
                        record = "Std_" + section + plant + "_Total"
                    keys.append((report_name, record[4:124], record, row))
                elif section in ("14", "73"):
                    if trim(label[:16 if section == "14" else 17]) == ("Total Effluents" if section == "14" else "Total Effluent $"):
                        suffix = trim(label)
                    else:
                        plant = trim(label)
                        record = "Std_" + section + "_" + suffix + "_" + plant
                        keys.append((report_name, record[4:124], record, row))
                elif section in ("27", "28"):
                    if len(label) > 2:
                        plant = trim(label)
                    else:
                        day_text = trim(label)
                        suffix = "Day" + (day_text.zfill(2) if day_text.isdigit() else day_text)
                        record = "Std_" + section + "_" + plant + "_" + suffix
                        keys.append((report_name, record[4:124], record, row))
                elif section == "32":
                    for block_row in range(row, row + (effluents_count - 1) * 4 + 1, 4):
                        record = "Std_" + section + "_" + (column_a[block_row - 1] if block_row <= last_row else "")
                        keys.append((report_name, record[4:124], record, block_row + 2))
                    row = row + ((effluents_count - 1) * 4) + 3
                else:
                    record = "Std_" + section + "_" + trim(label)
                    keys.append((report_name, record[4:124], record, row))
        row += 1
    return keys, ""
def simulate_rollup_flags(key_texts, ru_rows):
    """What SetRollup.SetRollupFlags writes into KeyedData columns E / F / G: for every RUIndex row whose key is in KeyedData column C (XMATCH, case-insensitive, first match) the three roll-up names are written to that KeyedData row. key_texts = the PrimaryKey of every KeyedData row in order. Returns (flags {KeyedData position: (E, F, G)}, RUIndex keys that are not in KeyedData - the macro stops with a type-mismatch error at the first of them)."""
    first_position = {}
    for position, text in enumerate(key_texts):
        first_position.setdefault(text.casefold(), position)
    flags, missing = {}, []
    for key, sec_gwh, plant_gwh, sec_cost in ru_rows:
        position = first_position.get(key.casefold())
        if position is None:
            missing.append(key)
        else:
            flags[position] = (sec_gwh, plant_gwh, sec_cost)
    return flags, missing
def predict_missing_index(lookups, key_texts, flags):
    """The #N/A counts of the MISSING INDEX CHECK for the lookup tabs: a lookup is #N/A when its text is not in the KeyedData column it searches (C = PrimaryKey from key_texts, E / F / G = the roll-up names of flags). Returns {sheet: [(row, column, text, KeyedData column)]} with only the lookups that fail."""
    columns = {"C": set(t.casefold() for t in key_texts), "E": set(), "F": set(), "G": set()}
    for sec_gwh, plant_gwh, sec_cost in flags.values():
        for letter, value in (("E", sec_gwh), ("F", plant_gwh), ("G", sec_cost)):
            if value not in (None, ""):
                columns[letter].add(str(value).casefold())
    failing = OrderedDict()
    for sheet_name, column, row_number, text, target in lookups:
        if text.casefold() not in columns.get(target, set()):
            failing.setdefault(sheet_name, []).append((row_number, column, text, target))
    return failing
def compare_keyed_data(predicted, reference):
    """Predicted KeyedData rows against a reference KeyedData (both lists of (ReportName, Account Name, PrimaryKey, Row)), grouped by <Std|Rat>_<section>: rows in each, keys in both (case-insensitive), keys only in the reference, keys only in the prediction, and rows in both whose ReportName / Account Name differ. Returns an OrderedDict group -> counts."""
    group_of = lambda key: "_".join(str(key).split("_", 2)[:2])
    predicted_by_key = {str(r[2]).casefold(): r for r in predicted}
    reference_by_key = {str(r[2]).casefold(): r for r in reference}
    summary = OrderedDict()
    for source, name in ((reference, "reference"), (predicted, "predicted")):
        for r in source:
            summary.setdefault(group_of(r[2]), Counter())[name] += 1
    for key, r in reference_by_key.items():
        counts = summary[group_of(r[2])]
        if key in predicted_by_key:
            counts["both"] += 1
            counts["name differs"] += int((str(predicted_by_key[key][0] or "").strip(), predicted_by_key[key][1]) != (str(r[0] or "").strip(), r[1]))
        else:
            counts["reference only"] += 1
    for key, r in predicted_by_key.items():
        if key not in reference_by_key:
            summary[group_of(r[2])]["predicted only"] += 1
    return summary
def report_table_spans(rows, is_ratings):
    """{table number (Standard) or section name (Ratings): (title line index, index after its last line)} for a finished report file."""
    titles, header_positions = find_report_titles(rows, is_ratings)
    spans = OrderedDict()
    for position, index in enumerate(titles):
        name = re.match(r"^\s*\(\s*(\d+[a-z]?)\s*\)", rows[index][0], flags=re.I).group(1).lower() if not is_ratings else rows[index][0].strip()
        spans[name] = (index, titles[position + 1] if position + 1 < len(titles) else len(rows))
    return spans
def add_zero_rows(rows, is_ratings, keys):
    """Append a row of zeros for every key '<Std|Rat>_<section>_<label>' of keys at the end of its table / section (a Ratings section that does not exist is created at the end of the file, with the month-header row of the first section). Only for tables the macro keys row by row, plus the plant rows of tables 3 and 6 (not tables 14, 27, 28, 32, 73 or the fuel rows of 3 and 6). Returns (new rows, keys added, keys that could not be added with the reason)."""
    rows = [list(cells) for cells in rows]
    spans = report_table_spans(rows, is_ratings)
    added, refused = [], []
    additions = OrderedDict()
    for key in keys:
        section, label = key.split("_", 2)[1], key.split("_", 2)[2]
        plant_row = (not is_ratings) and section.lower() in ("3", "6") and label.endswith("_Total") and "_" not in label[:-6]
        if (not is_ratings) and ((section.lower() in ("14", "27", "28", "32", "73") or (section.lower() in ("3", "6") and not plant_row)) or section.lower() not in spans):
            refused.append((key, "the table is built differently by the macro" if section.lower() in ("3", "6", "14", "27", "28", "32", "73") else "the table is not in the file"))
        else:
            additions.setdefault(section if is_ratings else section.lower(), []).append((key, label[:-6] if plant_row else label))
    month_pattern = re.compile(r"^\s*(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec|Tot)[-\s]?\d{2,4}\s*$", re.I)
    header = next((cells for cells in rows if month_header_position(cells, month_pattern) is not None), None)
    value_count = (len(header) - month_header_position(header, month_pattern)) if header else 79
    new_sections = [name for name in additions if name not in spans]
    for name, items in sorted(additions.items(), key=lambda item: -(spans[item[0]][1] if item[0] in spans else len(rows) + 1)):
        if name in spans:
            end = spans[name][1]
            while end > spans[name][0] + 1 and all(c.strip() == "" for c in rows[end - 1]):
                end -= 1
            rows[end:end] = [["  " + label] + ["0"] * value_count for key, label in items]
            added.extend(key for key, label in items)
    for name in new_sections:
        rows += [[], [" " + name]] + ([list(header)] if header else []) + [["  " + label] + ["0"] * value_count for key, label in additions[name]]
        added.extend(key for key, label in additions[name])
    return rows, added, refused
def count_effluent_blocks(rows):
    """Number of effluent blocks (a heading line with only a label) in table 32 of a Standard report: the number Control!C24 'Number of Effluent Types' must hold, because the macro reads that many blocks, 4 lines apart, and jumps past them."""
    spans = report_table_spans(rows, False)
    if "32" not in spans:
        return 0
    return sum(1 for cells in rows[spans["32"][0] + 1:spans["32"][1]] if len(cells) > 0 and cells[0].strip() != "" and not any(c.strip() != "" for c in cells[1:]))
def read_oprep_requirements(workbook_path):
    """Read from an OpRep_01 workbook what its macros and lookup tabs need (the workbook is only read): the number of effluent types (Control), the columns the MISSING INDEX CHECK counts, every lookup formula of the checked tabs that searches a KeyedData column (XMATCH, also when it points to another workbook: [1]KeyedData) together with the text it looks up, and the RUIndex roll-up table. Returns a dict: effluents_count, check_sheets (sheet -> counted column pairs), lookups [(sheet, column, row, text, KeyedData column)], external_lookups (sheet -> number of lookups that point to ANOTHER workbook), ru_rows [(key, SecRollUpGWh, PlantRollUpGWh, SecRollUp$000)]."""
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=False)
    requirements = {"effluents_count": 8, "check_sheets": OrderedDict(), "lookups": [], "ru_rows": [], "external_lookups": Counter()}
    for row in workbook["Control"].iter_rows(min_row=1, max_row=60, max_col=11, values_only=True):
        if isinstance(row[1], str) and "number of effluent types" in row[1].lower() and isinstance(row[2], (int, float)):
            requirements["effluents_count"] = int(row[2])
        if isinstance(row[8], str) and "COUNTIFS" in row[8].upper():
            for sheet_name, first_column, last_column in re.findall(r"COUNTIFS\(\s*'?([^'!()]+)'?!\$?([A-Z]+):\$?([A-Z]+)\s*,\s*\"#N/A\"", row[8], flags=re.I):
                requirements["check_sheets"].setdefault(sheet_name, []).append((first_column.upper(), last_column.upper()))
    lookup_pattern = re.compile(r"XMATCH\(\s*\$?([A-Z]+)\$?(\d+)\s*,\s*(\[\d+\])?KeyedData!\$?([A-Z]+):\$?[A-Z]+\s*\)", re.I)
    for sheet_name, column_pairs in requirements["check_sheets"].items():
        if sheet_name not in workbook.sheetnames:
            continue
        counted = [column for first_column, last_column in column_pairs if column_index_from_string(last_column) <= 6 for column in get_column_letter_range(first_column, last_column)]
        if len(counted) == 0:
            continue
        sheet_rows = [list(r) for r in workbook[sheet_name].iter_rows(min_row=1, max_row=workbook[sheet_name].max_row, max_col=6, values_only=True)]
        for row_number, cells in enumerate(sheet_rows, start=1):
            for column in counted:
                formula = cells[column_index_from_string(column) - 1] if column_index_from_string(column) <= len(cells) else None
                found = lookup_pattern.search(formula) if isinstance(formula, str) else None
                if found is None:
                    continue
                if found.group(3):
                    requirements["external_lookups"][sheet_name] += 1
                text = sheet_rows[int(found.group(2)) - 1][column_index_from_string(found.group(1)) - 1]
                if text not in (None, ""):
                    requirements["lookups"].append((sheet_name, column, row_number, str(text), found.group(4).upper()))
    if "RUIndex" in workbook.sheetnames:
        requirements["ru_rows"] = [(str(r[1]), r[2], r[3], r[4]) for r in workbook["RUIndex"].iter_rows(min_row=2, max_row=workbook["RUIndex"].max_row, max_col=5, values_only=True) if r[1] not in (None, "")]
    workbook.close()
    return requirements
def get_column_letter_range(first_column, last_column):
    """Column letters from first_column to last_column (for example 'B' to 'D' -> ['B', 'C', 'D'])."""
    return [get_column_letter(number) for number in range(column_index_from_string(first_column), column_index_from_string(last_column) + 1)]
def read_keyed_data_reference(workbook_path):
    """The first four columns (ReportName, Account Name, PrimaryKey, Row) of the KeyedData tab of a workbook, for every row that has a key."""
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=True)
    reference = [tuple(r) for r in workbook["KeyedData"].iter_rows(min_row=2, max_row=workbook["KeyedData"].max_row, max_col=4, values_only=True) if r[2] not in (None, "")]
    workbook.close()
    return reference
def excel_cell_text(text):
    """What VBA reads from a CSV field after Excel opened it: a plain number loses its formatting ('01' -> '1'), everything else stays text."""
    if re.fullmatch(r"[-+]?\d+(\.\d+)?", text):
        number = float(text)
        return str(int(number)) if number.is_integer() else repr(number)
    return text
def format_macro_title(title_text):
    """' ( 1) System Summary' form of a Standard table title: one leading space so that '(' is the 2nd character (CreateStandardKeys only recognises a title then) and the section number right-aligned to 2 characters, as RT Sim writes it. Returns None when the text is not a table title (the '(1) Change Case File = ...' lines contain '=')."""
    found = re.match(r"^\s*\(\s*(\d+[a-z]?)\s*\)\s*(.*)$", title_text, flags=re.I)
    return None if (found is None or "=" in title_text) else " (" + found.group(1).rjust(2) + ") " + found.group(2)
def format_macro_month_cell(text):
    """Month header cell as RT Sim writes it: ' Jan-2026 ' (4-digit year, one space each side, so Excel keeps it as text and Control!F10 can read the year from the last 4 characters), ' Tot-2026 ', '    Total '. Any other text is returned unchanged."""
    found = re.fullmatch(r"\s*(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec|Tot)[-\s]?(\d{2}|\d{4})\s*", text, flags=re.I)
    if found:
        return " " + found.group(1).capitalize() + "-" + ("20" + found.group(2) if len(found.group(2)) == 2 else found.group(2)) + " "
    return "    Total " if text.strip().lower() == "total" else text
def macro_rating_section_name(text, rules):
    """The Ratings section name the macro recognises (exact spelling) for a section name of the report, by the first rule (letters / digits prefix, macro name) that fits; None when no rule fits."""
    key = re.sub(r"[^a-z0-9]", "", text.lower())
    return next((name for prefix, name in rules if key.startswith(prefix)), None)
def find_report_titles(rows, is_ratings):
    """Line indexes (0-based) of the table titles (Standard) or section titles (Ratings: one-cell line directly above a month-header row), in file order."""
    month_pattern = re.compile(r"^\s*(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec|Tot)[-\s]?\d{2,4}\s*$", re.I)
    header_positions = [month_header_position(cells, month_pattern) for cells in rows]
    titles = []
    for index, cells in enumerate(rows):
        if len([c for c in cells if c.strip() != ""]) == 1 and len(cells) > 0 and cells[0].strip() != "":
            if (is_ratings and index + 1 < len(rows) and header_positions[index + 1] is not None) or ((not is_ratings) and format_macro_title(cells[0]) is not None):
                titles.append(index)
    return titles, header_positions
def make_macro_ready_rows(rows, is_ratings, first_title_row, rating_rules):
    """Make a Standard or Ratings report readable for the OpRep_01 macros without touching a number: blank lines so that the first title is on first_title_row (the macros read from row 26 and Control takes the start year from B28), Standard titles as ' ( 1) Title', Ratings section names as the macro spells them, month headers as padded text. Returns (new rows, changes [(kind, original line, old text, new text)], layout note)."""
    rows = [list(cells) for cells in rows]
    titles, header_positions = find_report_titles(rows, is_ratings)
    changes = []
    layout_note = ""
    if len(titles) > 0:
        shift = first_title_row - (titles[0] + 1)
        if shift > 0:
            rows = [[] for _ in range(shift)] + rows
            header_positions = [None] * shift + header_positions
            titles = [t + shift for t in titles]
            changes.append(("blank lines added at the top", 0, "", str(shift)))
        elif shift < 0 and count_leading_blank_rows(rows) >= -shift:
            rows = rows[-shift:]
            header_positions = header_positions[-shift:]
            titles = [t + shift for t in titles]
            changes.append(("blank lines removed from the top", 0, str(-shift), ""))
        elif shift < 0:
            layout_note = f"the first title is on line {titles[0] + 1}, below row {first_title_row}, and the lines above it are not blank: nothing was removed"
    for index in titles:
        old = rows[index][0]
        new = (" " + macro_rating_section_name(old, rating_rules)) if (is_ratings and macro_rating_section_name(old, rating_rules) is not None) else (old if is_ratings else format_macro_title(old))
        if new != old:
            rows[index][0] = new
            changes.append(("section name" if is_ratings else "table title", index + 1, old, new))
    for index, offset in enumerate(header_positions):
        if offset is not None:
            changed_cells = 0
            for position in range(offset, len(rows[index])):
                new = format_macro_month_cell(rows[index][position])
                if new != rows[index][position]:
                    rows[index][position] = new
                    changed_cells += 1
            if changed_cells > 0:
                changes.append(("month header cells", index + 1, "", f"{changed_cells} cells"))
    return rows, changes, layout_note
def simulate_macro_keys(rows, is_ratings, effluents_count, first_row=26):
    """What CreateKeys.CreateStandardKeys / CreateRatingKeys of OpRep_01 writes into KeyedData columns A-D for a report file, row by row exactly as the macro reads it (column A only, from row 26 to the last used row). Returns (keys [(ReportName, Account Name, PrimaryKey, Row)], error text or '')."""
    last_row = len(rows)
    while last_row > 0 and all(c == "" for c in rows[last_row - 1]):
        last_row -= 1
    column_a = [excel_cell_text(cells[0]) if len(cells) > 0 else "" for cells in rows[:last_row]]
    trim = lambda text: text.strip(" ")
    keys = []
    report_name, section, plant, suffix = "", "", "", ""
    row = first_row
    while row <= last_row:
        label = column_a[row - 1]
        if trim(label) != "":
            if is_ratings:
                if trim(label) in ("On-peak Mon-Sat", "Off-peak 23-6 Mon-Sun", "Sunday On-peak", "ATC Mon-Sun"):
                    report_name = trim(label)
                else:
                    keys.append(("Rating Report", trim(label), "Rat_" + report_name + "_" + trim(label), row))
            elif label.find("(") + 1 == 2:
                if label.find(")", 1) < 0:
                    return keys, f"row {row}: the table title has no ')': the macro stops with a run-time error"
                section = trim(label[2:label.find(")", 1)])
                report_name = trim(label)
            else:
                if section in ("3", "6"):
                    if trim(label[:5]) == "":
                        suffix = "_" + trim(label)
                        record = "Std_" + section + plant + suffix
                    else:
                        plant = "_" + trim(label)
                        record = "Std_" + section + plant + "_Total"
                    keys.append((report_name, record[4:124], record, row))
                elif section in ("14", "73"):
                    if trim(label[:16 if section == "14" else 17]) == ("Total Effluents" if section == "14" else "Total Effluent $"):
                        suffix = trim(label)
                    else:
                        plant = trim(label)
                        record = "Std_" + section + "_" + suffix + "_" + plant
                        keys.append((report_name, record[4:124], record, row))
                elif section in ("27", "28"):
                    if len(label) > 2:
                        plant = trim(label)
                    else:
                        day_text = trim(label)
                        suffix = "Day" + (day_text.zfill(2) if day_text.isdigit() else day_text)
                        record = "Std_" + section + "_" + plant + "_" + suffix
                        keys.append((report_name, record[4:124], record, row))
                elif section == "32":
                    for block_row in range(row, row + (effluents_count - 1) * 4 + 1, 4):
                        record = "Std_" + section + "_" + (column_a[block_row - 1] if block_row <= last_row else "")
                        keys.append((report_name, record[4:124], record, block_row + 2))
                    row = row + ((effluents_count - 1) * 4) + 3
                else:
                    record = "Std_" + section + "_" + trim(label)
                    keys.append((report_name, record[4:124], record, row))
        row += 1
    return keys, ""
def simulate_rollup_flags(key_texts, ru_rows):
    """What SetRollup.SetRollupFlags writes into KeyedData columns E / F / G: for every RUIndex row whose key is in KeyedData column C (XMATCH, case-insensitive, first match) the three roll-up names are written to that KeyedData row. key_texts = the PrimaryKey of every KeyedData row in order. Returns (flags {KeyedData position: (E, F, G)}, RUIndex keys that are not in KeyedData - the macro stops with a type-mismatch error at the first of them)."""
    first_position = {}
    for position, text in enumerate(key_texts):
        first_position.setdefault(text.casefold(), position)
    flags, missing = {}, []
    for key, sec_gwh, plant_gwh, sec_cost in ru_rows:
        position = first_position.get(key.casefold())
        if position is None:
            missing.append(key)
        else:
            flags[position] = (sec_gwh, plant_gwh, sec_cost)
    return flags, missing
def predict_missing_index(lookups, key_texts, flags):
    """The #N/A counts of the MISSING INDEX CHECK for the lookup tabs: a lookup is #N/A when its text is not in the KeyedData column it searches (C = PrimaryKey from key_texts, E / F / G = the roll-up names of flags). Returns {sheet: [(row, column, text, KeyedData column)]} with only the lookups that fail."""
    columns = {"C": set(t.casefold() for t in key_texts), "E": set(), "F": set(), "G": set()}
    for sec_gwh, plant_gwh, sec_cost in flags.values():
        for letter, value in (("E", sec_gwh), ("F", plant_gwh), ("G", sec_cost)):
            if value not in (None, ""):
                columns[letter].add(str(value).casefold())
    failing = OrderedDict()
    for sheet_name, column, row_number, text, target in lookups:
        if text.casefold() not in columns.get(target, set()):
            failing.setdefault(sheet_name, []).append((row_number, column, text, target))
    return failing
def compare_keyed_data(predicted, reference):
    """Predicted KeyedData rows against a reference KeyedData (both lists of (ReportName, Account Name, PrimaryKey, Row)), grouped by <Std|Rat>_<section>: rows in each, keys in both (case-insensitive), keys only in the reference, keys only in the prediction, and rows in both whose ReportName / Account Name differ. Returns an OrderedDict group -> counts."""
    group_of = lambda key: "_".join(str(key).split("_", 2)[:2])
    predicted_by_key = {str(r[2]).casefold(): r for r in predicted}
    reference_by_key = {str(r[2]).casefold(): r for r in reference}
    summary = OrderedDict()
    for source, name in ((reference, "reference"), (predicted, "predicted")):
        for r in source:
            summary.setdefault(group_of(r[2]), Counter())[name] += 1
    for key, r in reference_by_key.items():
        counts = summary[group_of(r[2])]
        if key in predicted_by_key:
            counts["both"] += 1
            counts["name differs"] += int((str(predicted_by_key[key][0] or "").strip(), predicted_by_key[key][1]) != (str(r[0] or "").strip(), r[1]))
        else:
            counts["reference only"] += 1
    for key, r in predicted_by_key.items():
        if key not in reference_by_key:
            summary[group_of(r[2])]["predicted only"] += 1
    return summary
def report_table_spans(rows, is_ratings):
    """{table number (Standard) or section name (Ratings): (title line index, index after its last line)} for a finished report file."""
    titles, header_positions = find_report_titles(rows, is_ratings)
    spans = OrderedDict()
    for position, index in enumerate(titles):
        name = re.match(r"^\s*\(\s*(\d+[a-z]?)\s*\)", rows[index][0], flags=re.I).group(1).lower() if not is_ratings else rows[index][0].strip()
        spans[name] = (index, titles[position + 1] if position + 1 < len(titles) else len(rows))
    return spans
def add_zero_rows(rows, is_ratings, keys):
    """Append a row of zeros for every key '<Std|Rat>_<section>_<label>' of keys at the end of its table / section (a Ratings section that does not exist is created at the end of the file, with the month-header row of the first section). Only for tables the macro keys row by row, plus the plant rows of tables 3 and 6 (not tables 14, 27, 28, 32, 73 or the fuel rows of 3 and 6). Returns (new rows, keys added, keys that could not be added with the reason)."""
    rows = [list(cells) for cells in rows]
    spans = report_table_spans(rows, is_ratings)
    added, refused = [], []
    additions = OrderedDict()
    for key in keys:
        section, label = key.split("_", 2)[1], key.split("_", 2)[2]
        plant_row = (not is_ratings) and section.lower() in ("3", "6") and label.endswith("_Total") and "_" not in label[:-6]
        if (not is_ratings) and ((section.lower() in ("14", "27", "28", "32", "73") or (section.lower() in ("3", "6") and not plant_row)) or section.lower() not in spans):
            refused.append((key, "the table is built differently by the macro" if section.lower() in ("3", "6", "14", "27", "28", "32", "73") else "the table is not in the file"))
        else:
            additions.setdefault(section if is_ratings else section.lower(), []).append((key, label[:-6] if plant_row else label))
    month_pattern = re.compile(r"^\s*(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec|Tot)[-\s]?\d{2,4}\s*$", re.I)
    header = next((cells for cells in rows if month_header_position(cells, month_pattern) is not None), None)
    value_count = (len(header) - month_header_position(header, month_pattern)) if header else 79
    new_sections = [name for name in additions if name not in spans]
    for name, items in sorted(additions.items(), key=lambda item: -(spans[item[0]][1] if item[0] in spans else len(rows) + 1)):
        if name in spans:
            end = spans[name][1]
            while end > spans[name][0] + 1 and all(c.strip() == "" for c in rows[end - 1]):
                end -= 1
            rows[end:end] = [["  " + label] + ["0"] * value_count for key, label in items]
            added.extend(key for key, label in items)
    for name in new_sections:
        rows += [[], [" " + name]] + ([list(header)] if header else []) + [["  " + label] + ["0"] * value_count for key, label in additions[name]]
        added.extend(key for key, label in additions[name])
    return rows, added, refused
def count_effluent_blocks(rows):
    """Number of effluent blocks (a heading line with only a label) in table 32 of a Standard report: the number Control!C24 'Number of Effluent Types' must hold, because the macro reads that many blocks, 4 lines apart, and jumps past them."""
    spans = report_table_spans(rows, False)
    if "32" not in spans:
        return 0
    return sum(1 for cells in rows[spans["32"][0] + 1:spans["32"][1]] if len(cells) > 0 and cells[0].strip() != "" and not any(c.strip() != "" for c in cells[1:]))
def simulate_prepared_reports(prep, effluents_used, assumed_keys, ru_rows, lookups):
    """Run the macro simulation on every prepared report of prep (report -> dict with 'rows' and 'is_ratings'); the keys and the macro error text of each report are stored in its dict ('keys', 'macro_error'). Returns (keyed rows of all reports, key texts including the keys assumed present, roll-up flags, RUIndex keys missing from KeyedData, predicted #N/A lookups per tab)."""
    for item in prep.values():
        item["keys"], item["macro_error"] = simulate_macro_keys(item["rows"], item["is_ratings"], effluents_used)
    keyed = [k for item in prep.values() for k in item["keys"]]
    key_texts = [k[2] for k in keyed] + list(assumed_keys)
    flags, ru_missing = simulate_rollup_flags(key_texts, ru_rows)
    return keyed, key_texts, flags, ru_missing, predict_missing_index(lookups, key_texts, flags)
def read_keyed_data_reference_fast(workbook_path, last_column="D"):
    """Same result as read_keyed_data_reference (the first four columns of every row of the KeyedData tab that has a PrimaryKey in column C, as tuples), but read straight from the sheet XML: only the first cells of every row are looked at, so the 48 MB tab is read in about a second instead of parsing every one of its 1.5 million cells. Whenever anything is not exactly the layout this reader expects (another cell type, a date-formatted number, a cell without its reference, a missing part) the original read_keyed_data_reference is used instead, so the result never differs."""
    try:
        import xml.etree.ElementTree as ET
        from openpyxl.styles.numbers import BUILTIN_FORMATS, is_date_format
        main_ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
        relationship_ns = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"
        unescape_xml = lambda text: re.sub(r"&(#x[0-9a-fA-F]+|#[0-9]+|lt|gt|amp|quot|apos);", lambda m: {"lt": "<", "gt": ">", "amp": "&", "quot": '"', "apos": "'"}.get(m.group(1)) or chr(int(m.group(1)[2:], 16) if m.group(1)[1] == "x" else int(m.group(1)[1:])), text)
        with zipfile.ZipFile(workbook_path) as archive:
            names = set(archive.namelist())
            workbook_root = ET.fromstring(archive.read("xl/workbook.xml"))
            relationship_id = next(sheet.get(relationship_ns + "id") for sheet in workbook_root.iter(main_ns + "sheet") if sheet.get("name") == "KeyedData")
            target = next(rel.get("Target") for rel in ET.fromstring(archive.read("xl/_rels/workbook.xml.rels")) if rel.get("Id") == relationship_id)
            sheet_path = target.lstrip("/") if target.startswith("/") else "xl/" + target
            custom_formats = {}
            date_styles = set()
            if "xl/styles.xml" in names:
                styles_root = ET.fromstring(archive.read("xl/styles.xml"))
                custom_formats = {int(node.get("numFmtId")): node.get("formatCode") for node in styles_root.iter(main_ns + "numFmt")}
                cell_formats = styles_root.find(main_ns + "cellXfs")
                for style_index, xf in enumerate(cell_formats if cell_formats is not None else []):
                    format_code = custom_formats.get(int(xf.get("numFmtId", 0))) or BUILTIN_FORMATS.get(int(xf.get("numFmtId", 0)))
                    if format_code and is_date_format(format_code):
                        date_styles.add(style_index)
            shared_strings = []
            if "xl/sharedStrings.xml" in names:
                strings_xml = archive.read("xl/sharedStrings.xml").decode("utf-8")
                for match in re.finditer(r"<si\b[^>]*?(?:/>|>(.*?)</si>)", strings_xml, re.S):
                    body = re.sub(r"<rPh\b.*?</rPh>", "", match.group(1) or "", flags=re.S)
                    pieces = re.findall(r"<t\b[^>]*?(?:/>|>(.*?)</t>)", body, re.S)
                    shared_strings.append(unescape_xml("".join(pieces).replace("\r\n", "\n").replace("\r", "\n")).replace("x005F_", ""))
            sheet_xml = archive.read(sheet_path).decode("utf-8")
        if sheet_xml.count("<c ") != sheet_xml.count('<c r="') or "<row " not in sheet_xml:
            raise ValueError("cells without a reference")
        dimension = re.search(r'<dimension ref="[A-Z]+\d+(?::[A-Z]+(\d+))?"', sheet_xml)
        max_row = int(dimension.group(1)) if dimension and dimension.group(1) else None
        cell_pattern = re.compile(r'<c r="([A-Z]+)(\d+)"([^>]*?)(?:/>|>(.*?)</c>)', re.S)
        reference = []
        for row_xml in sheet_xml.split("<row ")[1:]:
            row_values = {}
            for cell in cell_pattern.finditer(row_xml):
                column, row_number = cell.group(1), int(cell.group(2))
                if len(column) > 1 or column > last_column:
                    break
                attributes, body = cell.group(3), cell.group(4) or ""
                cell_type = re.search(r'\bt="(\w+)"', attributes)
                cell_type = cell_type.group(1) if cell_type else "n"
                style = re.search(r'\bs="(\d+)"', attributes)
                value_node = re.search(r"<v>(.*?)</v>", body, re.S)
                if cell_type == "inlineStr":
                    pieces = re.findall(r"<t\b[^>]*?(?:/>|>(.*?)</t>)", re.sub(r"<rPh\b.*?</rPh>", "", body, flags=re.S), re.S)
                    value = unescape_xml("".join(pieces).replace("\r\n", "\n").replace("\r", "\n"))
                elif value_node is None or value_node.group(1) == "":
                    value = None
                elif cell_type == "s":
                    value = shared_strings[int(value_node.group(1))]
                elif cell_type == "str":
                    value = unescape_xml(value_node.group(1).replace("\r\n", "\n").replace("\r", "\n"))
                elif cell_type == "n":
                    if style and int(style.group(1)) in date_styles:
                        raise ValueError("date-formatted number")
                    number_text = value_node.group(1)
                    value = float(number_text) if any(c in number_text for c in ".eE") else int(number_text)
                elif cell_type == "b":
                    value = bool(int(value_node.group(1)))
                elif cell_type == "e":
                    value = unescape_xml(value_node.group(1))
                else:
                    raise ValueError("unexpected cell type " + cell_type)
                row_values[column] = (row_number, value)
            if len(row_values) == 0:
                continue
            row_number = next(iter(row_values.values()))[0]
            if row_number < 2 or (max_row is not None and row_number > max_row):
                continue
            row = tuple(row_values[column][1] if column in row_values else None for column in "ABCDEFG"[:"ABCDEFG".index(last_column) + 1])
            if row[2] not in (None, ""):
                reference.append(row)
        return reference
    except Exception:
        return read_keyed_data_reference(workbook_path) if last_column == "D" else read_keyed_data_columns(workbook_path, last_column)
def read_oprep_requirements_quick(workbook_path):
    """read_oprep_requirements with the cached copy of the linked workbook not parsed (load_workbook(keep_links=False)): the lookup formulas, including the '[1]KeyedData' ones, are read as text exactly as before, so the result is identical; only the time spent on the link cache is saved."""
    import functools
    original_load_workbook = openpyxl.load_workbook
    openpyxl.load_workbook = functools.partial(original_load_workbook, keep_links=False)
    try:
        return read_oprep_requirements(workbook_path)
    finally:
        openpyxl.load_workbook = original_load_workbook
def read_workbook_cached(kind, workbook_path, reader):
    """reader(workbook_path), remembered for the next run in this session (plexos4_workbook_cache) as long as the file keeps its name, modified time and size. Returns (result, True when it came from the cache). A workbook that is open in Excel is reported in plain words."""
    cache = globals().setdefault("plexos4_workbook_cache", {})
    status = os.stat(workbook_path)
    cache_key = (kind, os.path.abspath(workbook_path), status.st_mtime_ns, status.st_size)
    for old_key in [k for k in cache if k[0] == kind and k != cache_key]:
        del cache[old_key]
    from_cache = cache_key in cache
    if not from_cache:
        try:
            cache[cache_key] = reader(workbook_path)
        except PermissionError:
            raise PermissionError(f"The workbook is open in Excel and cannot be read: {workbook_path}. Close it (or save a copy) and run this cell again.")
    return cache[cache_key], from_cache
################################################################################################################################################################################
#4.00 POST-LOAD TESTS (OpRep01 after the BLUE button)
################################################################################################################################################################################
POST_LOAD_ERROR_TEXTS = {"#N/A", "#REF!", "#VALUE!", "#DIV/0!", "#NAME?", "#NUM!", "#NULL!", "#SPILL!", "#CALC!"}
def is_date_value(value):
    """True for a date / datetime cell value (the name datetime is the CLASS in this file, so the module is imported here)."""
    import datetime as datetime_module
    return isinstance(value, (datetime_module.datetime, datetime_module.date))
def is_number_value(value):
    """True for an int / float cell value (a bool is not a number)."""
    return isinstance(value, (int, float)) and not isinstance(value, bool)
def sheet_value_text(value):
    """A cell value as comparable text: None = '', a whole number without '.0', everything else stripped text."""
    if value is None:
        return ""
    if isinstance(value, float) and math.isfinite(value) and value == int(value):
        return str(int(value))
    return str(value).strip()
def integer_or_none(value):
    """int(float(value)) or None when the value is not a number."""
    try:
        return int(float(value))
    except (TypeError, ValueError, OverflowError):
        return None
def year_of_value(value):
    """The year of a date, of an Excel date serial, of a plain year number (1900-2200) or of the first 4-digit number in a text; None when there is none."""
    if value is None:
        return None
    if is_date_value(value):
        return value.year
    if is_number_value(value):
        if math.isfinite(value) and float(value) == int(value) and 1900 <= int(value) <= 2200:
            return int(value)
        try:
            from openpyxl.utils.datetime import from_excel
            return from_excel(value).year
        except Exception:
            return None
    found = re.search(r"(\d{4})", str(value))
    return int(found.group(1)) if found else None
def read_cell_address(rows, address):
    """The value at an Excel address ('F10') of a list of row tuples (rows[0] = Excel row 1); None when the address is outside the rows."""
    from openpyxl.utils.cell import coordinate_to_tuple
    row_number, column_number = coordinate_to_tuple(address)
    return rows[row_number - 1][column_number - 1] if row_number - 1 < len(rows) and column_number - 1 < len(rows[row_number - 1]) else None
def cell_address(row_index, column_index):
    """Excel address of a 0-based row and column index (0, 5 -> 'F1')."""
    return f"{get_column_letter(column_index + 1)}{row_index + 1}"
def find_sheet_name(sheet_names, wanted_name):
    """The sheet whose name equals wanted_name (case-insensitive), else the first that contains it, else None."""
    for sheet_name in sheet_names:
        if sheet_name.casefold() == str(wanted_name).casefold():
            return sheet_name
    for sheet_name in sheet_names:
        if str(wanted_name).casefold() in sheet_name.casefold():
            return sheet_name
    return None
def read_sheet_rows(worksheet, max_row=None, max_col=None):
    """The values of a read-only worksheet as a list of row tuples (the sheet dimension recorded in the file is ignored, it is often wrong)."""
    try:
        worksheet.reset_dimensions()
    except Exception:
        pass
    return [tuple(row) for row in worksheet.iter_rows(max_row=max_row, max_col=max_col, values_only=True)]
def find_loaded_report_sheet(head_rows, report_key, wanted_name, sheet_titles):
    """The sheet that holds a loaded report: wanted_name when given, else the sheet whose cell A27 is a table title (Standard: starts with '(') or one of the four Ratings section names; a sheet with 'standard' / 'rating' in its name wins a tie. head_rows = {sheet: first rows}. None when there is no such sheet."""
    if wanted_name:
        return find_sheet_name(sheet_titles, wanted_name)
    rating_names = {"on-peak mon-sat", "off-peak 23-6 mon-sun", "sunday on-peak", "atc mon-sun"}
    hits = []
    for sheet_title, rows in head_rows.items():
        if len(rows) < 27 or len(rows[26]) == 0:
            continue
        title_cell = sheet_value_text(rows[26][0])
        if (report_key == "std" and title_cell.startswith("(")) or (report_key == "rat" and title_cell.casefold() in rating_names):
            hits.append(sheet_title)
    name_word = "standard" if report_key == "std" else "rating"
    hits.sort(key=lambda title: (name_word not in title.casefold(), title))
    return hits[0] if hits else None
def scan_error_cells(worksheet, max_col=6, max_examples=25):
    """Excel error values (#N/A, #REF!, ...) in the first max_col columns of a read-only worksheet. Returns the count and the first max_examples (address, error text)."""
    error_count, examples = 0, []
    for row_index, row in enumerate(read_sheet_rows(worksheet, max_col=max_col)):
        for column_index, value in enumerate(row):
            if isinstance(value, str) and value.strip() in POST_LOAD_ERROR_TEXTS:
                error_count += 1
                if len(examples) < max_examples:
                    examples.append((cell_address(row_index, column_index), value.strip()))
    return error_count, examples
def read_missing_index_cells(workbook_path, control_sheet_name="Control", max_row=60, max_col=11):
    """Where the MISSING INDEX CHECK counts are: the Control cells whose formula is COUNTIFS('<tab>'!A:C,"#N/A") (the same formulas read_oprep_requirements reads). Returns an OrderedDict tab -> Control cell address."""
    cells = OrderedDict()
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=False, keep_links=False)
    try:
        control_title = find_sheet_name(workbook.sheetnames, control_sheet_name)
        if control_title is None:
            return cells
        for row_number, row in enumerate(workbook[control_title].iter_rows(min_row=1, max_row=max_row, max_col=max_col, values_only=True), start=1):
            for column_number, value in enumerate(row, start=1):
                if isinstance(value, str) and "COUNTIFS" in value.upper():
                    for found in re.findall(r"COUNTIFS\(\s*'?([^'!()]+)'?!\$?([A-Z]+):\$?([A-Z]+)\s*,\s*\"#N/A\"", value, flags=re.I):
                        cells.setdefault(found[0], f"{get_column_letter(column_number)}{row_number}")
    finally:
        workbook.close()
    return cells
def read_loaded_oprep(workbook_path, keyed_sheet_name, control_sheet_name, report_sheet_names, check_sheet_names):
    """Read a SAVED OpRep01 workbook (values, not formulas; KeyedData is read separately by read_keyed_data_reference_fast): the sheet names, the first 200 x 20 cells of the Control tab, the Control cells of the MISSING INDEX CHECK, the sheet that holds each loaded report (Standard / Ratings) with all its rows, and the Excel error values of the first 6 columns of every tab in check_sheet_names. Returns a dict: titles, keyed_title, control_title, control, missing_index_cells, report_titles, reports, errors."""
    missing_index_cells = read_missing_index_cells(workbook_path, control_sheet_name)
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=True, keep_links=False)
    try:
        sheet_titles = [worksheet.title for worksheet in workbook.worksheets]
        keyed_title, control_title = find_sheet_name(sheet_titles, keyed_sheet_name), find_sheet_name(sheet_titles, control_sheet_name)
        head_rows = {title: read_sheet_rows(workbook[title], max_row=30, max_col=2) for title in sheet_titles if title not in (keyed_title, control_title)}
        report_titles_found = OrderedDict((report_key, find_loaded_report_sheet(head_rows, report_key, report_sheet_names.get(report_key), sheet_titles)) for report_key in ("std", "rat"))
        loaded = {"titles": sheet_titles, "keyed_title": keyed_title, "control_title": control_title, "control": [], "missing_index_cells": missing_index_cells, "report_titles": report_titles_found, "reports": {}, "errors": OrderedDict()}
        if control_title is not None:
            loaded["control"] = read_sheet_rows(workbook[control_title], max_row=200, max_col=20)
        for report_key, report_title in report_titles_found.items():
            if report_title is not None:
                loaded["reports"][report_key] = read_sheet_rows(workbook[report_title])
        wanted_check = {name.casefold() for name in check_sheet_names}
        for sheet_title in sheet_titles:
            if sheet_title.casefold() in wanted_check:
                loaded["errors"][sheet_title] = scan_error_cells(workbook[sheet_title])
        return loaded
    finally:
        workbook.close()
def read_keyed_data_columns(workbook_path, last_column="G"):
    """Slow fallback of read_keyed_data_reference_fast for more than 4 columns: columns A to last_column of every KeyedData row that has a PrimaryKey in column C (header row skipped), each row padded with None to the full width."""
    width = column_index_from_string(last_column)
    workbook = openpyxl.load_workbook(workbook_path, read_only=True, data_only=True, keep_links=False)
    try:
        worksheet = workbook["KeyedData"]
        rows = [tuple(row) + (None,) * (width - len(row)) for row in read_sheet_rows(worksheet, max_col=width)[1:]]
    finally:
        workbook.close()
    return [row for row in rows if row[2] not in (None, "")]
def build_loaded_key_records(keyed_rows):
    """The KeyedData rows of the loaded workbook (columns A to G) as records (position, ReportName, Account Name, PrimaryKey, report row, (E, F, G roll-up names)), all as comparable text / int."""
    records = []
    for position, row in enumerate(keyed_rows, start=1):
        row = tuple(row) + (None,) * max(0, 7 - len(row))
        records.append((position, sheet_value_text(row[0]), sheet_value_text(row[1]), sheet_value_text(row[2]), integer_or_none(row[3]), tuple(sheet_value_text(value) for value in row[4:7])))
    return records
def build_predicted_key_index(keyed, flags):
    """The KeyedData the preprocessing predicted as {casefolded PrimaryKey: (ReportName, Account Name, report row, (E, F, G), PrimaryKey)} (the first of a repeated key wins, like the XMATCH of the macros) and the number of repeated keys. flags = {position in keyed: (E, F, G)}."""
    predicted, repeated_count = OrderedDict(), 0
    for position, key_row in enumerate(keyed):
        key = str(key_row[2]).strip().casefold()
        if key in predicted:
            repeated_count += 1
            continue
        predicted[key] = (sheet_value_text(key_row[0]), sheet_value_text(key_row[1]), integer_or_none(key_row[3]), tuple(sheet_value_text(value) for value in tuple(flags.get(position, (None, None, None)))[:3]), str(key_row[2]))
    return predicted, repeated_count
def add_post_load_mismatch(mismatches, max_stored, check_name, sheet_name, location, expected, found, kind):
    """Remember one difference (check, sheet, location, expected, found, kind) while fewer than max_stored are stored (the counts of the checks are always complete)."""
    if len(mismatches) < max_stored:
        mismatches.append((check_name, sheet_name, location, expected, found, kind))
def compare_loaded_keyed_data(loaded_records, predicted, key_prefixes, mismatches, max_stored):
    """The KeyedData the macros wrote against the predicted one, for the keys that start with one of key_prefixes (casefolded, for example ('std_', 'rat_'); the fixed / variable cost keys of the workbook are not compared). Returns a dict: loaded_by_key, repeated (keys that appear twice), loaded_only, predicted_only, name_differs, row_differs, flag_differs (the lists hold the loaded records; predicted_only holds PrimaryKeys). Every difference is added to mismatches."""
    loaded_by_key, repeated = OrderedDict(), []
    for record in loaded_records:
        key = record[3].casefold()
        if not key.startswith(key_prefixes):
            continue
        if key in loaded_by_key:
            repeated.append(record[3])
        else:
            loaded_by_key[key] = record
    loaded_only = [record for key, record in loaded_by_key.items() if key not in predicted]
    predicted_only = [values[4] for key, values in predicted.items() if key not in loaded_by_key]
    name_differs, row_differs, flag_differs = [], [], []
    for key, record in loaded_by_key.items():
        if key not in predicted:
            continue
        predicted_report, predicted_account, predicted_row, predicted_flags, _ = predicted[key]
        if (record[1], record[2]) != (predicted_report, predicted_account):
            name_differs.append(record)
            add_post_load_mismatch(mismatches, max_stored, "KeyedData vs prediction", "KeyedData", record[3], f"A / B = {predicted_report} | {predicted_account}", f"A / B = {record[1]} | {record[2]}", "ReportName / Account Name differs")
        if record[4] != predicted_row:
            row_differs.append(record)
            add_post_load_mismatch(mismatches, max_stored, "KeyedData vs prediction", "KeyedData", record[3], f"D = {predicted_row}", f"D = {record[4]}", "report row (column D) differs")
        if record[5] != predicted_flags:
            flag_differs.append(record)
            add_post_load_mismatch(mismatches, max_stored, "KeyedData vs prediction", "KeyedData", record[3], f"E / F / G = {predicted_flags}", f"E / F / G = {record[5]}", "roll-up names (E / F / G) differ")
    for record in loaded_only:
        add_post_load_mismatch(mismatches, max_stored, "KeyedData vs prediction", "KeyedData", record[3], "(not predicted)", record[3], "key only in the loaded workbook")
    for primary_key in predicted_only:
        add_post_load_mismatch(mismatches, max_stored, "KeyedData vs prediction", "KeyedData", primary_key, primary_key, "(missing)", "predicted key missing in the loaded workbook")
    return {"loaded_by_key": loaded_by_key, "repeated": repeated, "loaded_only": loaded_only, "predicted_only": predicted_only, "name_differs": name_differs, "row_differs": row_differs, "flag_differs": flag_differs}
def compare_loaded_report_sheet(report_label, sheet_name, csv_rows, sheet_rows, first_data_row, rel_tol, abs_tol, mismatches, max_stored):
    """Every non-empty cell of a ready report file (csv_rows, from line first_data_row) against the same cell of the loaded sheet (sheet_rows, from the same row): a number must be the same number (within rel_tol / abs_tol), any other text the same text (a plain number in a label cell is compared the way Excel reads it, '01' = '1'). Differences: number differs, value / text missing in the sheet, number stored as text, text instead of a number, converted to a date, text differs. Returns a Counter of the differences, the cells compared, the sum of the numbers in the file, the sum of the numbers in the sheet and the number of non-empty sheet cells that are not in the file."""
    counts, compared, csv_sum, sheet_sum, extra_cells = Counter(), 0, 0.0, 0.0, 0
    number_pattern = re.compile(r"^-?\d+(\.\d+)?([eE][-+]?\d+)?$")
    for row_index in range(first_data_row - 1, max(len(csv_rows), len(sheet_rows))):
        csv_row = csv_rows[row_index] if row_index < len(csv_rows) else []
        sheet_row = sheet_rows[row_index] if row_index < len(sheet_rows) else ()
        for column_index, cell_text in enumerate(csv_row):
            expected = cell_text.strip()
            if expected == "":
                continue
            actual = sheet_row[column_index] if column_index < len(sheet_row) else None
            compared += 1
            kind = None
            if column_index > 0 and number_pattern.match(expected):
                expected_number = float(expected)
                csv_sum += expected_number
                if is_number_value(actual):
                    sheet_sum += actual
                    if abs(actual - expected_number) > abs_tol + rel_tol * abs(expected_number):
                        kind = "number differs"
                elif actual is None or str(actual).strip() == "":
                    kind = "value missing in the sheet"
                elif is_date_value(actual):
                    kind = "converted to a date"
                else:
                    try:
                        float(str(actual).strip())
                        kind = "number stored as text"
                    except ValueError:
                        kind = "text instead of a number"
            elif actual is None or str(actual).strip() == "":
                kind = "text missing in the sheet"
            elif is_date_value(actual):
                kind = "converted to a date"
            elif sheet_value_text(actual) != excel_cell_text(expected):
                kind = "text differs"
            if kind is not None:
                counts[kind] += 1
                add_post_load_mismatch(mismatches, max_stored, f"{report_label} report vs ready file", sheet_name, cell_address(row_index, column_index), expected, "" if actual is None else str(actual), kind)
        extra_cells += sum(1 for value in sheet_row[len(csv_row):] if value is not None and str(value).strip() != "")
    return counts, compared, csv_sum, sheet_sum, extra_cells
def find_workbook_external_links(workbook_path):
    """The external-link parts (xl/externalLinks/*.xml) of a workbook, i.e. links such as '[1]KeyedData' to another workbook. Returns the list of parts and an error text ('' when the file could be inspected)."""
    try:
        with zipfile.ZipFile(workbook_path) as workbook_zip:
            return [name for name in workbook_zip.namelist() if name.startswith("xl/externalLinks/") and name.endswith(".xml")], ""
    except Exception as error:
        return [], f"{type(error).__name__}: {error}"
def format_file_time(timestamp):
    """A file time stamp as 'YYYY-MM-DD HH:MM:SS' (local time)."""
    import datetime as datetime_module
    return datetime_module.datetime.fromtimestamp(timestamp).strftime("%Y-%m-%d %H:%M:%S")
################################################################################################################################################################################
#4.00, 4.01, & 4.04
################################################################################################################################################################################
def sheet_rows_as_text_rows(sheet_rows):
    """The rows of a loaded report sheet (values read from the saved OpRep_01 workbook) as the list of text rows read_csv_rows gives for a CSV file, so the section parser of PlexOS-4.01 / 4.04 can read the sheet exactly like a file: None = '', text as it is (padding kept), a date as ISO text, a number as its repr(); trailing empty cells are cut. Row n of the result is row n of the sheet."""
    text_rows = []
    for sheet_row in sheet_rows:
        cells = ["" if value is None else (value if isinstance(value, str) else (value.isoformat() if is_date_value(value) else repr(value))) for value in sheet_row]
        while cells and cells[-1] == "":
            cells.pop()
        text_rows.append(cells)
    return text_rows
def index_keyed_sections(loaded_records):
    """The PrimaryKeys of a loaded KeyedData tab grouped by report type and section: {('std', '<table number>') or ('rat', '<rating section>'): [record, ...]}, both casefolded. A key is 'Std_<table>_<row value>' or 'Rat_<section>_<row value>' (the keys the OpRep_01 macros write); other keys (the FC / VC cost keys) are not indexed. loaded_records = build_loaded_key_records(...)."""
    keys_by_section = defaultdict(list)
    for record in loaded_records:
        key_parts = record[3].split("_", 2)
        if len(key_parts) == 3 and key_parts[0].casefold() in ("std", "rat"):
            keys_by_section[(key_parts[0].casefold(), key_parts[1].strip().casefold())].append(record)
    return keys_by_section
def check_keyed_section_records(keys_by_section, report_kind, section_key, first_line, last_line, labels_in_section):
    """Is one section of the loaded report represented in the KeyedData tab? Every section that has labelled rows needs at least one KeyedData key, and every key of the section must point (column D) to a row of the loaded sheet that lies inside the section (first_line = its title line, last_line = the last line before the next title; both 1-based). Returns passed, key_count, outside_section (the keys that point elsewhere) and a detail text."""
    section_records = keys_by_section.get((report_kind, str(section_key).strip().casefold()), [])
    outside_section = [record for record in section_records if record[4] is None or not (first_line < record[4] <= last_line)]
    has_keys = len(section_records) > 0 or labels_in_section == 0
    detail = f"KeyedData tab: {len(section_records)} key(s) for this {'rating section' if report_kind == 'rat' else 'table'}, {len(outside_section)} pointing outside lines {first_line + 1}-{last_line}" + ("" if has_keys else f"; none, but the section has {labels_in_section} labelled row(s)") + (f"; e.g. {outside_section[0][3]} -> row {outside_section[0][4]}" if outside_section else "")
    return has_keys and len(outside_section) == 0, len(section_records), outside_section, detail
def find_section_last_line(title_lines, first_line, row_count):
    """The last line (1-based) of the section that starts on first_line: the line before the next section title of title_lines (1-based), or the last line of the sheet."""
    later_titles = [line for line in title_lines if line > first_line]
    return (min(later_titles) - 1) if later_titles else row_count
def strip_path_text(answer):
    """A path answer without surrounding spaces / quotes, and without the r"..." prefix of a path pasted from code."""
    answer = str(answer).strip().strip('"').strip("'")
    if answer[:2].lower() in ('r"', "r'"):
        answer = answer[2:].strip('"').strip("'")
    return answer
def normalize_key_text(text):
    """Text reduced to lower-case letters and digits for loose matching: the 'Â' of a mis-read non-breaking space is dropped, accents are decomposed (NFKD), the text is case-folded and everything that is not a letter or a digit is removed."""
    return re.sub(r"[^0-9a-z]+", "", unicodedata.normalize("NFKD", str(text).replace("\u00c2", "")).casefold())
def squeeze_text(text):
    """Lower-case text without any whitespace (the non-breaking space included), without the 'Â' of a mis-read non-breaking space and without zero-width characters."""
    return re.sub(r"[\s\u00c2\u200b\ufeff]+", "", text.lower())
def build_key(prefix, section, rest):
    """The KeyedData key the macro writes: <prefix>_<section number>_<row value> (the section number is trimmed)."""
    return prefix + "_" + section.strip() + "_" + rest
def show_hidden_chars(text, spaces_as_dots=False):
    """Text with every non-breaking space shown as [nbsp] (and, with spaces_as_dots, every space as a middle dot)."""
    text = text.replace("\u00a0", "[nbsp]")
    return text.replace(" ", "\u00b7") if spaces_as_dots else text
def find_first_hit(candidates, make_key, lookup):
    """The first candidate whose key make_key(candidate) is in lookup (a dict: key -> list of KeyedData records). Returns (records, candidate), or (None, None) when no candidate is found."""
    for candidate in candidates:
        lookup_key = make_key(candidate)
        if lookup_key in lookup:
            return lookup[lookup_key], candidate
    return None, None
def effluent_heading_check(text, table_id):
    """(is the text the effluent heading the macro recognises for this table, the heading it expects): table 14 'Total Effluents', every other effluent group table 'Total Effluent $'."""
    heading_name = "Total Effluents" if table_id == "14" else "Total Effluent $"
    prefix_length = 16 if table_id == "14" else 17
    return text[:prefix_length].strip() == heading_name, heading_name
def add_table_sheet(workbook, sheet_name, headers, rows, widths, header_fill, header_font, fills=None, fill_column=None, auto_filter=True):
    """Create a sheet: the header row (fill / font), every row of rows, one filled cell per row (fills = a fill or None for each row, fill_column = its 1-based column), the column widths, the first row frozen and (auto_filter) a filter over the data. Returns the sheet."""
    worksheet = workbook.create_sheet(sheet_name)
    worksheet.append(headers)
    style_cells(worksheet[1], header_fill, header_font)
    for position, row_values in enumerate(rows):
        worksheet.append(row_values)
        if fills is not None and fills[position] is not None:
            worksheet.cell(row=worksheet.max_row, column=fill_column).fill = fills[position]
    set_openpyxl_column_widths(worksheet, widths)
    worksheet.freeze_panes = "A2"
    if auto_filter:
        worksheet.auto_filter.ref = worksheet.dimensions
    return worksheet
def write_csv_file(csv_path, header, rows, encoding="utf-8"):
    """Write a CSV file: the header line, then every row (csv module, newline='' so the line endings are the csv default). Returns the path."""
    with open(csv_path, "w", newline="", encoding=encoding) as csv_file:
        csv_writer = csv.writer(csv_file)
        csv_writer.writerow(header)
        csv_writer.writerows(rows)
    return csv_path
def count_padding(text):
    """(number of leading spaces, number of trailing spaces) of a text."""
    return len(text) - len(text.lstrip()), len(text) - len(text.rstrip())
def add_header_sheet(workbook, sheet_name, headers, fill, font, wrap=False):
    """Create a sheet whose first row is the header row (fill / font, optionally wrapped at the top) and return the sheet."""
    worksheet = workbook.create_sheet(sheet_name)
    worksheet.append(headers)
    style_cells(worksheet[1], fill, font, wrap)
    return worksheet
def color_pass_fail(worksheet, row, column, passed, pass_fill, fail_fill):
    """Fill one cell with pass_fill when passed is True, else with fail_fill."""
    worksheet.cell(row=row, column=column).fill = pass_fill if passed else fail_fill
def prompt_for_existing_file(prompt_text, input_tag, max_attempts=5):
    """Ask for a file path until it points to an existing file (at most max_attempts asks, then FileNotFoundError naming input_tag). Quotes are removed (clean_user_path) and so is the r"..." prefix of a path pasted from code. Returns the path."""
    for attempt_number in range(max_attempts):
        input_answer = clean_user_path(prompt_text)
        if input_answer[:2].lower() in ('r"', "r'"):
            input_answer = input_answer[2:].strip('"').strip("'")
        if os.path.isfile(input_answer):
            return input_answer
        print(f"   File not found: '{input_answer}'")
    raise FileNotFoundError(f"No file was found for input {input_tag} after {max_attempts} attempts: '{input_answer}'")
def normalize_label(text, steps, strip_parentheses=False):
    """Normalize a label: strip, lower case, optionally drop the text in parentheses, apply every (pattern, replacement) of steps in order, strip again."""
    text = str(text).strip().lower()
    if strip_parentheses:
        text = re.sub(r"\([^)]*\)", "", text)
    for pattern, replacement in steps:
        text = re.sub(pattern, replacement, text)
    return text.strip()
def alias_label(text, steps, alias_norm, strip_parentheses=False):
    """normalize_label, then the alias table alias_norm (normalized alias -> normalized name) applied."""
    label_key = normalize_label(text, steps, strip_parentheses)
    return alias_norm.get(label_key, label_key)
def show_spaces(text):
    """Text with every padding / double space shown as middle dots (a single space between words is kept)."""
    tokens = re.findall(r" +|[^ ]+", text)
    return "".join("\u00b7" * len(token) if token[0] == " " and (len(token) >= 2 or k == 0 or k == len(tokens) - 1) else token for k, token in enumerate(tokens))
def style_cells(cells, fill=None, font=None, wrap=False):
    """Apply fill / font / wrapped top alignment to every cell of a row (for example ws[1] or ws[ws.max_row])."""
    for cell in cells:
        if fill is not None:
            cell.fill = fill
        if font is not None:
            cell.font = font
        if wrap:
            cell.alignment = Alignment(wrap_text=True, vertical="top")
def append_bold_row(worksheet, values, size=None):
    """Append a row and make its first cell bold (optionally with a font size)."""
    worksheet.append(values)
    worksheet.cell(row=worksheet.max_row, column=1).font = Font(bold=True, size=size)
def read_csv_rows(csv_path, as_dicts=False):
    """Read a CSV file as a list of rows (list of lists), or as a list of dictionaries (as_dicts=True)."""
    with open(csv_path, "r", newline="", encoding="utf-8-sig", errors="replace") as csv_file:
        return list(csv.DictReader(csv_file)) if as_dicts else list(csv.reader(csv_file))
def month_header_position(cells, month_pattern):
    """Position of the first month cell of a row when only blanks / numbers / 'index' come before it, else None."""
    for position in range(len(cells)):
        if month_pattern.match(cells[position]):
            return position if all(c.strip() == "" or c.strip().isdigit() or c.strip().lower() == "index" for c in cells[:position]) else None
    return None
def count_leading_blank_rows(rows):
    """Number of completely blank rows at the top of a list of CSV rows."""
    blank_count = 0
    while blank_count < len(rows) and all(c.strip() == "" for c in rows[blank_count]):
        blank_count += 1
    return blank_count
def lowercase_set_or_none(names):
    """Set of the lower-cased names, or None when the list is empty (None = no selection)."""
    return set(x.lower() for x in names) if len(names) > 0 else None
def print_banner(title, char="=", width=100, blank_line=False):
    """Print a title between two lines of char (optionally after a blank line)."""
    if blank_line:
        print()
    print(char * width)
    print(title)
    print(char * width)
def heading_record(tab, row, col, label):
    """Parsed group-heading record of a table / section."""
    return {"tab": tab, "row": row, "col": col, "label": label, "group": label, "kind": "heading", "pos": 0}
def new_label_candidate(table_name, kind, row, col, old, tab, via="", fuzzy=False, group="", l=""):
    """A label-cell candidate (title / header / heading / row) in its starting state: new = old, state 'no_table'."""
    return {"table": table_name, "kind": kind, "row": row, "col": col, "old": old, "new": old, "state": "no_table", "via": via, "fuzzy": fuzzy, "rt_row": "", "rt_label": "", "group": group, "l": l, "hint": "", "tab": tab}
def section_exception(section, px_title, px_line, exception_type, step, detail):
    """One exception-report row of the section mapping test (Exception Id / Test Case / Report are added afterwards)."""
    return {"Section": section, "PLEXOS Title": px_title, "PLEXOS Line": px_line, "Exception Type": exception_type, "Step": step, "Detail": detail}
def section_mapping_row(record, tc_id, report_label, status_text):
    """One row of the section mapping results (CSV and the Section Mapping sheet use the same row)."""
    return [tc_id, f"{report_label} Report", record["id"], record["px_title"], record["px_line"], record["kd_key"] if record["kd_key"] is not None else "", record["kd_title"], record["kd_line"] if record["kd_line"] is not None else "", record["method"],
            status_text[record["destination_defined"]], status_text[record["structure_valid"]], record["structure_detail"], status_text[record["category_valid"]], record["category_detail"], status_text[record["traceable"]], record["trace_detail"], record["rows"], record["rows_traced"], status_text[record["section_pass"]]]
def simulate_everything():
    simulated = OrderedDict()
    for report, item in prep.items():
        item["keys"], item["macro_error"] = simulate_macro_keys(item["rows"], item["is_ratings"], effluents_used)
        simulated[report] = item["keys"]
    keyed = [k for report in prep for k in prep[report]["keys"]]
    key_texts = [k[2] for k in keyed] + assumed_keys
    flags, ru_missing = simulate_rollup_flags(key_texts, oprep["ru_rows"])
    return keyed, key_texts, flags, ru_missing, predict_missing_index(oprep["lookups"], key_texts, flags)
################################################################################################################################################################################
#4.01 / 4.04 SECTION MAPPING AGAINST THE LOADED OpRep_01 WORKBOOK
################################################################################################################################################################################
def sheet_rows_as_text_rows(sheet_rows):
    """The rows of a loaded report sheet (values read from the saved OpRep_01 workbook) as the list of text rows read_csv_rows gives for a CSV file, so the section parser of PlexOS-4.01 / 4.04 can read the sheet exactly like a file: None = '', text as it is (padding kept), a date as ISO text, a number as its repr(); trailing empty cells are cut. Row n of the result is row n of the sheet."""
    text_rows = []
    for sheet_row in sheet_rows:
        cells = ["" if value is None else (value if isinstance(value, str) else (value.isoformat() if is_date_value(value) else repr(value))) for value in sheet_row]
        while cells and cells[-1] == "":
            cells.pop()
        text_rows.append(cells)
    return text_rows
def index_keyed_sections(loaded_records):
    """The PrimaryKeys of a loaded KeyedData tab grouped by report type and section: {('std', '<table number>') or ('rat', '<rating section>'): [record, ...]}, both casefolded. A key is 'Std_<table>_<row value>' or 'Rat_<section>_<row value>' (the keys the OpRep_01 macros write); other keys (the FC / VC cost keys) are not indexed. loaded_records = build_loaded_key_records(...)."""
    keys_by_section = defaultdict(list)
    for record in loaded_records:
        key_parts = record[3].split("_", 2)
        if len(key_parts) == 3 and key_parts[0].casefold() in ("std", "rat"):
            keys_by_section[(key_parts[0].casefold(), key_parts[1].strip().casefold())].append(record)
    return keys_by_section
def check_keyed_section_records(keys_by_section, report_kind, section_key, first_line, last_line, labels_in_section):
    """Is one section of the loaded report represented in the KeyedData tab? Every section that has labelled rows needs at least one KeyedData key, and every key of the section must point (column D) to a row of the loaded sheet that lies inside the section (first_line = its title line, last_line = the last line before the next title; both 1-based). Returns passed, key_count, outside_section (the keys that point elsewhere) and a detail text."""
    section_records = keys_by_section.get((report_kind, str(section_key).strip().casefold()), [])
    outside_section = [record for record in section_records if record[4] is None or not (first_line < record[4] <= last_line)]
    has_keys = len(section_records) > 0 or labels_in_section == 0
    detail = f"KeyedData tab: {len(section_records)} key(s) for this {'rating section' if report_kind == 'rat' else 'table'}, {len(outside_section)} pointing outside lines {first_line + 1}-{last_line}" + ("" if has_keys else f"; none, but the section has {labels_in_section} labelled row(s)") + (f"; e.g. {outside_section[0][3]} -> row {outside_section[0][4]}" if outside_section else "")
    return has_keys and len(outside_section) == 0, len(section_records), outside_section, detail
def find_section_last_line(title_lines, first_line, row_count):
    """The last line (1-based) of the section that starts on first_line: the line before the next section title of title_lines (1-based), or the last line of the sheet."""
    later_titles = [line for line in title_lines if line > first_line]
    return (min(later_titles) - 1) if later_titles else row_count
################################################################################################################################################################################
################################################################################################################################################################################

################################################################################################################################################################################
################################################################################################################################################################################

################################################################################################################################################################################
################################################################################################################################################################################

################################################################################################################################################################################
################################################################################################################################################################################