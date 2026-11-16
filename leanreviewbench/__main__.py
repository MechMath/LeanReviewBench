import argparse
import json
from pathlib import Path
from .artifacts import install
from .dataset import Dataset
from .evaluate import score, restore_sources


def main():
    parser=argparse.ArgumentParser(description='LeanReviewBench offline preview tools')
    commands=parser.add_subparsers(dest='command',required=True)
    p=commands.add_parser('prepare');p.add_argument('--manifest',type=Path,required=True);p.add_argument('--artifacts',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--references',action='store_true');p.add_argument('--reproduction',action='store_true')
    p=commands.add_parser('validate');p.add_argument('--data',type=Path,required=True)
    p=commands.add_parser('task');p.add_argument('--data',type=Path,required=True);p.add_argument('--id',required=True);p.add_argument('--output',type=Path)
    p=commands.add_parser('score');p.add_argument('--data',type=Path,required=True);p.add_argument('--predictions',type=Path,required=True);p.add_argument('--references',type=Path,required=True);p.add_argument('--allow-provisional',action='store_true');p.add_argument('--allow-partial',action='store_true')
    p=commands.add_parser('restore');p.add_argument('--data',type=Path,required=True);p.add_argument('--id',required=True);p.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        if args.command=='prepare':
            roles=['inputs']+(['references'] if args.references else [])+(['reproduction'] if args.reproduction else [])
            result=install(args.manifest,args.artifacts,args.output,roles)
        elif args.command=='validate':result=Dataset(args.data).validate()
        elif args.command=='task':
            result=Dataset(args.data).task(args.id)
            if args.output:
                args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');return
        elif args.command=='restore':result=restore_sources(args.data,args.id,args.output)
        else:result=score(Dataset(args.data),args.predictions,args.references,args.allow_provisional,args.allow_partial)
        print(json.dumps(result,ensure_ascii=False,indent=2))
    except (ValueError,OSError,KeyError) as exc:parser.exit(2,str(exc)+'\n')

if __name__=='__main__':main()
