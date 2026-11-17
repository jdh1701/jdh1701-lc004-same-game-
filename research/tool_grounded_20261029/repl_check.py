"""Replay exact proof source and exercise incremental acceptance/rejection."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--repl',type=Path,required=True)
args=parser.parse_args()
source=(REPO/'research/ContinuationSummaryObstruction.lean').read_text()
commands=[{'cmd':source},
 {'cmd':'example : LC004.RunSolvable (LC004.encode (LC004.continuationWordLeft ++ [2])) := LC004.continuation_left_wins_after_C','env':0},
 {'cmd':'example : (1 : Nat) = 2 := by rfl','env':0},
 {'cmd':'example : (2 : Nat) = 2 := by rfl','env':0}]
request='\n\n'.join(json.dumps(c) for c in commands)+'\n\n'
result=subprocess.run([str(args.repl.resolve())],cwd=REPO,input=request,text=True,capture_output=True,timeout=90,check=True)
decoder=json.JSONDecoder();text=result.stdout;responses=[]
while text.strip():
    response,end=decoder.raw_decode(text.lstrip());responses.append(response);text=text.lstrip()[end:]
assert len(responses)==4
for i,(response,expected) in enumerate(zip(responses,[True,True,False,True])):
    accepted=not response.get('sorries') and not any(m.get('severity')=='error' for m in response.get('messages',[]))
    assert accepted==expected,(i,response)
    if accepted:
        assert 'sorryAx' not in json.dumps(response)
assert 'CONTINUATION AUDIT PASS' in json.dumps(responses[0])
(ROOT/'repl-transcript.json').write_text(json.dumps(dict(
    source_sha256=hashlib.sha256(source.encode()).hexdigest(),
    commands=commands,responses=responses,
    rejected_environment_reused=False,
    status='Three intended acceptances; false theorem rejected; new theorem axiom audit passed'),indent=2)+'\n')
print('REPL CHECK PASS: exact source, incremental proof, false theorem rejected, clean environment reused')
