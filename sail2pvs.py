#! /usr/bin/env python3

import os
import json
import helper
import argparse
import shutil
from rewrite_handler import rewriteFiles


lem_path = os.path.join(helper.udir_path, 'lem')
ott_path = os.path.join(helper.udir_path, 'ott')
sail_path = os.path.join(helper.udir_path, 'sail')
sail_exec_path = os.path.join(sail_path, 'sail')
replace_pairs = ('../lem', lem_path)

json_path = os.path.join(helper.dir_path, 'tag.json')
data = None
with open(json_path) as json_file:
    data = json.load(json_file)


def generate_diff_patch(name, only_print):
    patch_info = data['patch']
    dest_dir = os.path.join(patch_info['dest_dir'], name)
    src_dir = os.path.join(patch_info['src_dir'], name)
    patch_path = patch_info['patch_path']
    cmd = 'diff -Naur '
    cmd += dest_dir + ' '
    cmd += src_dir
    cmd += ' > ' + os.path.join(patch_path, name + '.patch')
    print(cmd)
    if not only_print:
        helper.execute_command(cmd)


def backup_new_file(name, only_print):
    patch_info = data['patch']
    src_dir = os.path.join(patch_info['src_dir'], name)
    dest_dir = os.path.join(patch_info['dest_dir'], name)
    patch_path = patch_info['patch_path']
    src_files = list(filter(lambda f: f.endswith('.ml'), os.listdir(src_dir)))
    copy_files = []
    cmd = ''
    for file in src_files:
        if not os.path.exists(os.path.join(dest_dir, file)):
            copy_files.append(file)
    if copy_files:
        cmd += 'cp -f '
        cmd += ' '.join(list(map(lambda f: os.path.join(src_dir, f), copy_files)))
        cmd += ' ' + patch_path
    print(cmd)
    if not only_print and cmd:
        helper.execute_command(cmd)


def patch_path_to_absolute(file_path):
    data = ''
    with open(file_path, 'r') as f:
        lines = f.readlines()
        for line in lines:
            if line.startswith('diff -Naur '):
                data += line.replace(replace_pairs[0], replace_pairs[1])
            elif line.startswith('--- '):
                data += line.replace(replace_pairs[0], replace_pairs[1])
            elif line.startswith('+++ '):
                data += line.replace(replace_pairs[0], replace_pairs[1])
            else:
                data += line
    return data


def patch_lem_src(name):
    patch_info = data['patch']
    patch_path = os.path.join(helper.dir_path, os.path.join(patch_info['patch_path'], name))
    patch_data = patch_path_to_absolute(patch_path + '.patch')
    abs_patch_path = patch_path + '_abs.patch'
    helper.write_file(abs_patch_path, patch_data)
    cmd = 'patch -p0 -d / < ' + abs_patch_path + '; '
    cmd += 'rm ' + abs_patch_path + '; '
    return cmd


def setup_sail2pvs(only_print):
    cmd = patch_lem_src('src')
    cmd += patch_lem_src('library')
    cmd += 'cp ./patches/*.ml ' + os.path.join(lem_path, 'src') + '; '
    print(cmd)
    if not only_print:
        out = helper.execute_command(cmd)
        print(out)


def construct_sail_to_lem_cmd(sail_files, lem_flags, lem_libs_path, object_name):
    cmd = sail_exec_path
    cmd += ' -o ' + object_name + ' -lem '
    if lem_libs_path:
        cmd += '-lem_lib ' + lem_libs_path
    cmd += ' ' + lem_flags + ' '
    cmd += sail_files
    return cmd


def construct_from_lem_cmd(target_language, sail_src_path, target_dir, lem_src_files, lem_extra_libs):
    lem_executable = helper.preprocess_path(data['lem_executable'])
    cmd = lem_executable + ' -' + target_language + ' -outdir ' + target_dir
    cmd += ' ' + helper.add_prefix('-lib', helper.preprocess_path(lem_extra_libs))
    cmd += ' ' + helper.build_file_path(sail_src_path, lem_src_files)
    return cmd


def parse_library_to_pvs(library_name, only_print):
    lem_executable = helper.preprocess_path(data['lem_executable'])
    lem_library_data = data[library_name]
    pvs_library_path = os.path.join(helper.dir_path, lem_library_data['pvs_library_name'])
    if os.path.exists(pvs_library_path):
        shutil.rmtree(pvs_library_path)
    os.mkdir(pvs_library_path)
    cmd = 'cd ' + lem_library_data['library_path'] + '; '
    cmd += lem_executable + ' -pvs -outdir ' + pvs_library_path + ' '
    cmd += lem_library_data['lem_flags'] + ' '
    cmd += lem_library_data['lem_src_files'] + '; '
    cmd += 'cd ' + pvs_library_path + '; '
    cmd += 'rm -f *_aux.pvs; '
    print(cmd)
    if not only_print:
        helper.execute_command(cmd)
        rewriteFiles.rewrite_files(pvs_library_path, lem_library_data['special_prefix'])
        cmd = 'cp -f ./pvs_aux/* ' + pvs_library_path
        helper.execute_command(cmd)


def parse_sail_to_pvs(project_name, only_print):
    project_info = data[project_name]
    sail_src_path = helper.preprocess_path(project_info['sail_src_path'])
    sail_src_files = project_info['sail_src_files']
    lem_src_files = project_info['lem_src_files']
    lem_embedded_lib = project_info['lem_embedded_lib']
    lem_object_name = project_info['lem_object_name']
    target_dir = helper.preprocess_path(project_info['target_dir'])
    lem_flags = project_info['lem_flags']
    lem_source_libs = data['lem_source_libs']
    if not os.path.exists(target_dir):
        os.mkdir(target_dir)
    sail_to_lem_cmd = construct_sail_to_lem_cmd(sail_src_files, lem_flags, lem_embedded_lib, lem_object_name)
    lem_to_ocaml_cmd = construct_from_lem_cmd('ocaml', sail_src_path, target_dir, lem_src_files, lem_source_libs)
    lem_to_pvs_cmd = construct_from_lem_cmd('pvs', sail_src_path, target_dir, lem_src_files, lem_source_libs)
    cmd = 'cd ' + sail_src_path + '; '
    cmd += sail_to_lem_cmd + '; '
    cmd += 'cd ' + helper.dir_path + '; '
    cmd += lem_to_ocaml_cmd + '; '
    cmd += lem_to_pvs_cmd + '; '
    cmd += 'cd ' + target_dir + '; '
    cmd += 'rm -f *_aux.pvs; cd ..'
    print(cmd)
    if not only_print:
        helper.execute_command(cmd)
        rewriteFiles.rewrite_files(target_dir, '')


def clear(only_print):
    lem_lib_name = data['lem_library']['pvs_library_name']
    sail_lib_names = data['sail_libs']
    cmd = 'rm -f ./' + lem_lib_name + '/*.pvs; '
    for lib_name in sail_lib_names:
        target_dir = data[lib_name]['target_dir']
        cmd += 'rm -rf ' + target_dir + '; '
    print(cmd)
    if not only_print:
        helper.execute_command(cmd)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--setup', action='store_true', help='Setup the Sail2PVS parser environment')
    parser.add_argument('--patch', action='store_true',
                        help='Generate patches for same source code at different locations')
    parser.add_argument('--library', action='store_true',
                        help='Generate .pvs files for the Lem basic library')
    parser.add_argument('--parse', type=str,
                        help='Parse the information written in tag.json to PVS files under the given directory')
    parser.add_argument('--just_print', action='store_true',
                        help='Just print the command line that will be executed')
    parser.add_argument('--clear', action='store_true', help='Clear some directories')
    args = parser.parse_args()
    only_print = False
    if args.just_print:
        only_print = True
    if args.setup:
        setup_sail2pvs(only_print)
    elif args.patch:
        generate_diff_patch('src', only_print)
        generate_diff_patch('library', only_print)
        backup_new_file('src', only_print)
    elif args.library:
        parse_library_to_pvs('basic_library', only_print)
    elif args.parse:
        parse_sail_to_pvs(args.parse, only_print)
    elif args.clear:
        clear(only_print)

