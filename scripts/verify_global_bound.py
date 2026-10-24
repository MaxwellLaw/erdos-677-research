#!/usr/bin/env python3
"""Replay the exact arithmetic chain for the documented subgroup result.
Analytic theorems and full Mordell-Weil generation retain their stated boundaries.
"""
from pathlib import Path
import json, os, subprocess, sys, tempfile

if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):
    raise SystemExit('Certificate assertions must remain enabled.')
root=Path(__file__).resolve().parents[1]
source=root/'cas/global-bound'

def mathematical(obj):
    obj=dict(obj)
    obj.pop('python_version',None);obj.pop('python',None)
    return obj

def compare(candidate,expected):
    a,b=json.loads(candidate.read_text()),json.loads(expected.read_text())
    if mathematical(a)!=mathematical(b):
        raise SystemExit(f'Replay mismatch: {expected.name}')
    return a

with tempfile.TemporaryDirectory(prefix='erdos677-global-') as tmp:
    tmp=Path(tmp)
    def execute(label,cmd,filename=None,stdout_json=False):
        output=tmp/filename if filename else None
        proc=subprocess.run([sys.executable,*map(str,cmd)],cwd=root,text=True,
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if proc.returncode:
            print(proc.stdout,end='');raise SystemExit(proc.returncode)
        if stdout_json:output.write_text(proc.stdout)
        if output is not None:compare(output,source/filename)
        print('PASS:',label,flush=True)
    execute('prior exact height constants',[root/'scripts/verify_heights.py'])
    execute('algebraic height parameters',[source/'height_parameters.py'], 'height_parameters.json',True)
    for script,name,label in [
      ('certify_period_parameters.py','period_parameters.json','period-area parameters'),
      ('certify_david_constants.py','david_constants.json','David constants and initial cutoff'),
      ('certify_real_logs.py','real_logs.json','rigorous real-log intervals')]:
        execute(label,[source/script,'--output',tmp/name],name)
    execute('25 independently checked lattice-distance steps',[
      source/'verify_lattice_certificate.py','--logs',source/'real_logs.json',
      '--certificate',source/'lattice_reduction.json','--output',tmp/'lattice_verification.json'],
      'lattice_verification.json')
    execute('complete cyclic-group residual sieve',[
      source/'enumerate_residual.py','--bound-json',source/'lattice_reduction.json','--prime-count','30',
      '--output',tmp/'residual_enumeration.json'],'residual_enumeration.json')
    execute('independent complete-group translation sieve',[
      source/'verify_residual_independent.py','--bounds',source/'lattice_reduction.json',
      '--maps',root/'cas/verify_k6_maps.output.json','--basis-input',source/'real_logs.json',
      '--output',tmp/'residual_independent.json'],'residual_independent.json')
    first=json.loads((tmp/'residual_enumeration.json').read_text())
    second=json.loads((tmp/'residual_independent.json').read_text())
    p={tuple(c['pair']):c for c in first['curves']}
    s={tuple(c['pair']):c for c in second['curves']}
    assert p.keys()==s.keys()
    total=0
    for pair,a in p.items():
        b=s[pair];assert a['closed_bound']==b['bound']
        assert a['total_triples']==b['total_triples']==(2*a['closed_bound']+1)**3
        assert set(r['p'] for r in a['sieves']).isdisjoint(r['prime'] for r in b['sieves'])
        x={tuple(r['coefficients']):r for r in a['exact_survivors']}
        y={tuple(r['coefficients']):r for r in b['survivors']}
        assert x.keys()==y.keys()
        for triple,u in x.items():
            v=y[triple]
            assert u['status']==v['status'] and u['point']==v['point']
            assert u.get('inverse_values')==v.get('inverse')
            assert u['status'] in {'elliptic_identity','inverse_denominator_zero','below_target',
                                  'noninteger_inverse','nonsquare_inverse','even_square_root','gap_below_six'}
        total+=len(x)
    assert total==46
    print('PASS: both exhaustive implementations agree on all 46 residual points; no admissible pair.',flush=True)
