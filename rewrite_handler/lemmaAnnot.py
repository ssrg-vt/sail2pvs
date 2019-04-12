#! /usr/bin/env python3

# Add type variable declaration at the beginning of a PVS lemma

import re
from . import util


def split_lemma(lines):
    splits = lines.split(' LEMMA', 1)
    name = splits[0].rsplit(':', 1)[0].strip()
    type_variables = []
    if ']' in name:
        name_split = name.split('[')
        name = name_split[0]
        type_variables = list(map(lambda s: s.split(':')[0].strip(), name_split[1].split(']')[0].split(',')))
    content = splits[1].strip()
    return name, type_variables, content


def parse_type(t_def):
    t_split = list(map(lambda s: s.strip(), re.split('\[|\]|,|->', t_def)))
    type_variables = [t for t in t_split if t.istitle()]
    return type_variables


def find_type_variables(content):
    tvars = []
    splits = re.split('FORALL|EXISTS', content)
    for i in range(1, len(splits)):
        parts = splits[i].strip()
        if parts.startswith('(') and ':' in parts:
            parts_split = util.split_sep_bk(parts, ':')[0]
            arg_list = util.split_sep_bk(parts_split, ',')
            args = map(lambda s: s.split('(', 1)[1].rsplit(')', 1)[0].strip(), arg_list)
            args = list(map(lambda s: parse_type(s.split(':', 1)[1].strip()), args))
            args = util.flatten(args)
            tvars.extend(args)
    return tvars


def handle_lemma(name, tvars, content):
    new_tvars = find_type_variables(content)
    tvars = list(set(tvars) | set(new_tvars))
    tyvars = '[' + ', '.join(tvars) + ' : TYPE]' if tvars else ''
    return name + tyvars + ' : LEMMA ' + content


def construct_lemma(lines):
    (name, type_variables, content) = split_lemma(lines)
    return handle_lemma(name, type_variables, content)


if __name__ == '__main__':
    print(construct_lemma(
        'list_update_length : LEMMA FORALL (l : list[A]), (n : nat), (e : A) : (eqs(length(update(l)(n)(e)))(length(l)))'))
