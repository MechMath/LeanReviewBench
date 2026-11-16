import argparse
import json
from pathlib import Path
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from scripts.data.dataset import Dataset


def main():
    parser=argparse.ArgumentParser(description='Native LeanReviewBench project-case inspection and validation')
    commands=parser.add_subparsers(dest='command',required=True)
    p=commands.add_parser('validate');p.add_argument('--root',type=Path,default=Path('.'))
    p=commands.add_parser('inspect');p.add_argument('--root',type=Path,default=Path('.'));p.add_argument('--id',required=True)
    args=parser.parse_args()
    try:
        if args.command=='inspect':
            print(json.dumps(Dataset(args.root).project(args.id),ensure_ascii=False,indent=2))
        else:
            root=args.root.resolve()
            subprocess.run([sys.executable,str(root/'scripts/data/check_release_candidate.py')],cwd=root,check=True)
            print(json.dumps(Dataset(root).validate(),indent=2))
    except (ValueError,OSError,KeyError,subprocess.CalledProcessError) as exc:parser.exit(2,str(exc)+'\n')

if __name__=='__main__':main()
