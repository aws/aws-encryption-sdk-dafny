#!/usr/bin/env python3
 
import xml.etree.ElementTree as ET
import sys

def results_for_trx_file(file):
    return ET.parse(file).getroot().find("./{http://microsoft.com/schemas/VisualStudio/TeamTest/2010}Results") or []

results = [result for file in sys.argv[1:] for result in results_for_trx_file(file)]
sorted_by_duration = sorted(results, key=lambda result: result.attrib.get("duration", "00:00:00.0000000"), reverse=True)
for result in sorted_by_duration:
    print(f'{result.attrib.get("duration")}, {result.get("outcome")}, {result.attrib.get("testName")}')
