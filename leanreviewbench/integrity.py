"""Verify the uncompressed, Git-tracked dataset against its byte inventory."""
import hashlib
import json
from pathlib import Path, PurePosixPath
from .dataset import require


def file_hash(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()


def verify_files(manifest_path,data):
    manifest=json.loads(Path(manifest_path).read_text())
    require(manifest['schema_version']=='leanreviewbench-release-2','Unsupported release manifest')
    data=Path(data);seen=set();roles=set();total=0
    for directory in manifest['directories']:
        role=directory['role']
        require(role in ('inputs','references','reproduction') and role not in roles,'Unknown/duplicate directory role')
        require(directory['path']==role,'Unsafe directory path');roles.add(role);size=0
        for entry in directory['files']:
            name=PurePosixPath(entry['path'])
            require(not name.is_absolute() and '..' not in name.parts and str(name)==entry['path'] and name.parts,'Unsafe data path')
            relative=role+'/'+entry['path'];require(relative not in seen,'Duplicate inventory file');seen.add(relative)
            path=data/relative
            require(all(not p.is_symlink() for p in [data,path,*path.parents] if p!=data.parent),'Symlink in data path')
            require(path.is_file(),'Missing data file: '+relative)
            require(path.stat().st_size==entry['size'] and file_hash(path)==entry['sha256'],'Data hash/size mismatch: '+relative)
            size+=entry['size'];total+=1
        require(size==directory['size'],'Directory size mismatch')
    require(roles=={'inputs','references','reproduction'},'Incomplete directory roles')
    actual={p.relative_to(data).as_posix() for p in data.rglob('*') if p.is_file() or p.is_symlink()}
    require(actual==seen,'Unexpected data files')
    return dict(files=total,bytes=sum(d['size'] for d in manifest['directories']))
