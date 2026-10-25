#!/usr/bin/env python3
# Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
"""Independent exact HNF and quotient-charpoly checks on the class replay.
Default mode checks the saved audit record and does not write repository files.
"""
from pathlib import Path
from fractions import Fraction
from itertools import combinations
from math import gcd
import argparse,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
spec=importlib.util.spec_from_file_location('reviewed_class_checker',HERE/'verify_class_relations.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)

def det3(a):
    x,y,z=a
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])

oldhnf=module.hnf
stats={'hnf_calls':0,'maximal_minors_checked':0,'charpolys_checked':0}

def independently_audited_hnf(vectors):
    inputs=[list(row) for row in vectors]
    assert all(Fraction(z).denominator==1 for row in inputs for z in row)
    inputs=[[int(z) for z in row] for row in inputs]
    H=oldhnf(inputs);d=det3(H);assert d>0
    # Inclusion of input lattice in H lattice, by exact Cramer coordinates.
    for v in inputs:
        for i in range(3):
            replaced=[row[:] for row in H];replaced[i]=v
            assert det3(replaced)%d==0
    # The index of a full-rank integer row lattice is gcd of all maximal minors.
    g=0
    for rows in combinations(inputs,3):
        g=gcd(g,det3(rows));stats['maximal_minors_checked']+=1
    assert g==d
    stats['hnf_calls']+=1
    return H

module.hnf=independently_audited_hnf
oldcp=module.charpoly

def independently_audited_charpoly(M,p):
    result=oldcp(M,p);n=len(M);tr=sum(M[i][i] for i in range(n))
    if n==1:expected=[-tr,1]
    elif n==2:expected=[M[0][0]*M[1][1]-M[0][1]*M[1][0],-tr,1]
    else:
        assert n==3
        second=sum(M[i][i]*M[j][j]-M[i][j]*M[j][i] for i in range(3) for j in range(i+1,3))
        expected=[-det3(M),second,-tr,1]
    assert [x%p for x in expected]==result
    stats['charpolys_checked']+=1
    return result

module.charpoly=independently_audited_charpoly

def read_only_finish(path,data):
    # Do not propagate this audit's --write option to the class certificate.
    stored=path.read_bytes()
    assert json.loads(stored)==json.loads(json.dumps(data,default=str))
    return hashlib.sha256(stored).hexdigest()

module.finish=read_only_finish

def main():
    if not __debug__:raise SystemExit('Keep assertions enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='write only the audit summary JSON')
    args=parser.parse_args()
    module.main()
    actual=(HERE/'class_relation_checks.json').read_bytes()
    assert stats=={'hnf_calls':2470,'maximal_minors_checked':158676,'charpolys_checked':438}
    report={'status':'PASS','checked_class_certificate_sha256':hashlib.sha256(actual).hexdigest(),
        'reviewed_source_sha256':hashlib.sha256((HERE/'verify_class_relations.py').read_bytes()).hexdigest(),
        'auditor_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),**stats,
        'independence':'each HNF output checked by lattice inclusion plus gcd of every 3x3 minor; every quotient characteristic polynomial checked by independent degree<=3 formulas; full exact replay matches the saved class certificate'}
    path=HERE/'class_lattice_audit.json'
    if args.write:path.write_text(json.dumps(report,indent=2)+'\n')
    else:assert json.loads(path.read_text())==report
    print('PASS: independent audit of 2470 HNF outputs, 158676 maximal minors, and 438 quotient characteristic polynomials.')

if __name__=='__main__':main()
