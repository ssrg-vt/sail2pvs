#! /usr/bin/env python3

# -*- coding: utf-8 -*-
import os
from . import util
from . import parseFiles
from . import lemmaAnnot
from . import addMeasure
from . import patternRewrite
from . import parseFunction


S_STATE, S_TYPE, S_FUNCTION, S_LEMMA = range(4)


def rewrite_file(file_path, start_notation=''):
    parseFiles.parse_file(file_path)
    file_name = file_path.split('/')[-1]
    if not file_name.startswith(start_notation):
        return
    updated_content = ''
    with open(file_path) as f:
        lines = f.readlines()
        type_dec = []
        function_dec = ''
        lemma_dec = ''
        state = S_STATE
        for line in lines:
            if line.startswith('%'):
                updated_content += line
            elif state == S_STATE:
                if ':VAR' in line.replace(' ', ''):
                    updated_content += line
                elif 'DATATYPE' in line:
                    updated_content += line
                    state = S_TYPE
                elif 'LEMMA ' in line:
                    lemma_dec = line
                    state = S_LEMMA
                elif ':TYPE=' in line.replace(' ', '') or ':TYPE+=' in line.replace(' ',
                                                                                    '') or ':TYPE\n' in line.replace(
                        ' ', '') or (': THEORY' in line and ']' in line) or (util.constPat.search(
                        line) and '->' not in line and 'THEORY' not in line and 'LAMBDA' not in line and not line.endswith(
                        ',\n') and '(#' not in line):
                    updated_content += line
                elif (util.pvsDefPat.search(line) or util.constPat.search(line)) and ':' in line and '=' in line:
                    function_dec = line
                    state = S_FUNCTION
                else:
                    updated_content += line
            elif state == S_TYPE:
                updated_content += line
                to_continue = True
                if 'END ' in line:
                    state = S_STATE
                    to_continue = False
                if to_continue:
                    type_dec.append(line)
            elif state == S_LEMMA:
                to_continue = True
                if line.replace(' ', '') == '\n':
                    updated_content += lemmaAnnot.construct_lemma(lemma_dec)
                    updated_content += '\n\n'
                    state = S_STATE
                    to_continue = False
                if to_continue:
                    lemma_dec += line
            elif state == S_FUNCTION:
                to_continue = True
                if line.replace(' ', '') == '\n':
                    func_name, arg_list, fun_def, fun_content = parseFunction.process_function({}, function_dec)
                    fun_content = '\n' + patternRewrite.rewrite_pattern(fun_content, arg_list[:-1])
                    measure = addMeasure.handle_recursive(arg_list, fun_content) if 'RECURSIVE ' in fun_def else ''
                    updated_content += fun_def + ' = ' + fun_content + measure
                    updated_content += '\n\n'
                    state = S_STATE
                    to_continue = False
                if to_continue:
                    function_dec += line
            else:
                updated_content += '\n'
    with open(file_path, 'w+') as f:
        f.write(updated_content)


def pvs_lib_path():
    path_list = os.environ.get('PVS_LIBRARY_PATH').split(':')
    return path_list


def rewrite_files(lib_path, name_annot):
    lib_name = lib_path.split('/')[-1]
    parseFiles.gen_lib_deps(lib_path)
    file_list = list(filter(lambda name: '@' not in name, parseFiles.file_dict[lib_name]))
    for file_name in file_list:
        file_path = os.path.join(lib_path, file_name)
        try:
            rewrite_file(file_path, name_annot)
        except:
            util.logger.debug('Rewriting file fails for ' + file_name)


if __name__ == '__main__':
    rewrite_files('/home/cindy/Documents/Tools/Sail2PVS/OPEV_Basic', 'lem_')

