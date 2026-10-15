from pathlib import Path
import hashlib,json,subprocess
r=Path('/data/lean/tasks/pgm-integration')
d=r/'docs/validation/2026-10-11-pgm'
assert json.loads((d/'comparison.json').read_text())['result']=='pass'
base='a1f4d122949298a9f8dd465dd16f5680287cb275'
peer='6d17da20d7a7625333ecf87d23824f031a01a6ae'
bare='/home/ubuntu/git/StabilizerLearning.git'
def blob(rev,path):
 return subprocess.check_output(['git','--git-dir='+bare,'show',rev+':'+path])
files=[
 'StabilizerLearning/FiniteCopy/GramEnergy.lean',
 'StabilizerLearning/FiniteCopy/SupportedSynthesis.lean',
 'StabilizerLearning/Quantum/PureStateVectors.lean',
 'StabilizerLearning/FiniteCopy/ColumnMeasurement.lean',
 'StabilizerLearning/FiniteCopy/PrettyGoodMeasurement.lean',
 'StabilizerLearning/FiniteCopy/StabilizerPGM.lean',
 'lean-toolchain','lakefile.toml','lake-manifest.json','toolchain-lock.json',
 'StabilizerLearning/FixedConstraints/Rates.lean',
 'StabilizerLearning/FixedConstraints/Task.lean']
rows={}
for f in files:
 a,b=blob(base,f),blob(peer,f)
 assert a==b,f
 rows[f]=hashlib.sha256(a).hexdigest()
record={'result':'pass','pgm_math_freeze':base,'peer_unified_math_freeze':peer,
 'unchanged_files_sha256':rows,
 'scope':'Six accepted PGM modules, original public task/rate definitions and version locks are byte-identical in the independently coordinated final Main source.',
 'limitation':'This comparison is source compatibility evidence only. Acceptance of the complete Main belongs to the separate strict Mac/Linux check and fresh reproduction of the peer unified freeze. It does not claim those checks have completed.'}
(d/'peer-interface-preservation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
