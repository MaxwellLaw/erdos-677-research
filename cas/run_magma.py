#!/usr/bin/env python3
"""Submit one public mathematics script to the official Magma calculator.
The remote service may change version. Keep its version and complete raw output.
No claim about integral-point completeness is made by this runner.
"""
import argparse
import json
from pathlib import Path
import re
import urllib.request

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('script',type=Path)
p.add_argument('output',type=Path)
a=p.parse_args()
req=urllib.request.Request('https://calculator.magma-maths.org/execute',
    data=json.dumps({'code':a.script.read_text()}).encode(),
    headers={'Content-Type':'application/json'})
with urllib.request.urlopen(req,timeout=60) as response:
    raw=response.read()
a.output.write_bytes(raw)
r=json.loads(raw)
stdout=r.get('stdout','')
# The API has returned success=true despite top-level Magma runtime errors.
# Therefore inspect the actual transcript, not merely the JSON success flag.
failed=(not r.get('success') or r.get('exit_code')!=0 or r.get('truncated')
        or re.search(r'(?im)(runtime error|user error|syntax error|assertion failed)',stdout))
print(json.dumps({'version':r.get('magma',{}).get('version'),
                  'output':str(a.output),'passed_transport_checks':not bool(failed)}))
if failed:
    raise SystemExit('Magma returned an error or incomplete output; inspect the saved transcript.')
print(stdout)
