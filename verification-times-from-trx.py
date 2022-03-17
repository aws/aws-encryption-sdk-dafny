#!/usr/bin/env python3
 
import xml.etree.ElementTree as ET
import sys
import os

from datetime import datetime, timedelta

def results_for_trx_file(file):
    return ET.parse(file).getroot().find("./{http://microsoft.com/schemas/VisualStudio/TeamTest/2010}Results") or []

results = [result for file in sys.argv[1:] for result in results_for_trx_file(file)]
sorted_by_duration = sorted(results, key=lambda result: result.attrib.get("duration", "00:00:00.0000000"), reverse=True)
too_slow = []
threshold_string = os.environ.get("MAX_VERIFICATION_DURATION_SECONDS")
threshold = None
if threshold_string:
  threshold = int(threshold_string)
for result in sorted_by_duration:
    duration = result.attrib.get("duration")
    row = f'{duration}, {result.get("outcome")}, {result.attrib.get("testName")}'
    print(row)

    if threshold:
      # Chop off the fractions of seconds since strptime can't handle them well and they aren't relevant
      as_datetime = datetime.strptime(duration[:8], "%H:%M:%S")
      duration_in_seconds = timedelta(hours=as_datetime.hour, minutes=as_datetime.minute, seconds=as_datetime.second).total_seconds()
      if duration_in_seconds > threshold:
        too_slow.append(row)


if too_slow:
  print(f"\nERROR - these durations are over the MAX_VERIFICATION_DURATION_SECONDS threshold of {threshold}:\n")
  for row in too_slow:
    print(row)
  sys.exit(1)
