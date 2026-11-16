"""Verified, atomic local artifact installation; no implicit downloads."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile
from .dataset import require


def file_hash(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()


def install(manifest_path,artifact_directory,destination,roles=('inputs',)):
    manifest=json.loads(Path(manifest_path).read_text())
    require(manifest['schema_version']=='leanreviewbench-release-1','Unsupported release manifest')
    index={a['role']:a for a in manifest['artifacts']}
    require(set(roles)<=set(index),'Unknown artifact role')
    destination=Path(destination);destination.mkdir(parents=True,exist_ok=True)
    installed=[]
    for role in roles:
        artifact=index[role];relative=PurePosixPath(artifact['path'])
        require(len(relative.parts)==1 and relative.name not in ('.','..'),'Unsafe artifact path')
        path=Path(artifact_directory)/relative.name
        require(path.stat().st_size==artifact['size'] and file_hash(path)==artifact['sha256'],'Artifact hash/size mismatch: '+role)
        require(not (destination/role).exists(),'Destination already installed: '+role)
        expected={m['path']:m for m in artifact['members']}
        require(len(expected)==len(artifact['members']),'Duplicate manifest member')
        staging=Path(tempfile.mkdtemp(prefix='.install-',dir=destination))
        seen=set()
        try:
            with tarfile.open(path,'r|gz') as archive:
                for member in archive:
                    name=PurePosixPath(member.name)
                    require(not name.is_absolute() and '..' not in name.parts and str(name)==member.name,'Unsafe archive path')
                    require(member.isfile() and member.name in expected and member.name not in seen,'Unexpected archive member')
                    binding=expected[member.name]
                    require(member.size==binding['size'],'Archive member size mismatch')
                    output=staging/member.name;output.parent.mkdir(parents=True,exist_ok=True)
                    h=hashlib.sha256()
                    with archive.extractfile(member) as src, output.open('wb') as dst:
                        for chunk in iter(lambda:src.read(1024*1024),b''):h.update(chunk);dst.write(chunk)
                    require(h.hexdigest()==binding['sha256'],'Archive member hash mismatch')
                    seen.add(member.name)
            require(seen==set(expected),'Missing archive member')
            os.replace(staging,destination/role);installed.append(role)
        finally:
            if staging.exists():shutil.rmtree(staging)
    return dict(installed=installed,inputs=manifest['inputs'],version=manifest['version'])
