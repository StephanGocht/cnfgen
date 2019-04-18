#!/usr/bin/env python
# -*- coding:utf-8 -*-

from cnfformula.cnf import CNF

from cnfformula.cmdline import SimpleGraphHelper

from cnfformula.cmdline import register_cnfgen_subcommand
from cnfformula.families import register_cnf_generator

from cnfformula.graphs import enumerate_vertices, neighbors


@register_cnf_generator
def Roth(n, bound):
    F = CNF()

    def X(i):
        return "x_{{{0}}}".format(i)

    # Create variables
    for i in range(1, n+1):
        F.add_variable(X(i))

    # Conditions
    for i in range(1, n+1):
        for k in range(i+1, n+1):
            for j in range(k+1, n+1):
                if (i+j != 2*k):
                    continue
                F.add_clause([(False, X(i)), (False, X(j)), (False, X(k))])

    if bound:
        F.add_greater_or_equal([X(i) for i in range(1, n+1)], bound)

    return F


@register_cnfgen_subcommand
class RothCmdHelper(object):
    name = 'roth'
    description = 'Roth Set'

    @staticmethod
    def setup_command_line(parser):
        parser.add_argument('n', type=int)
        parser.add_argument('--bound', type=int)

    @staticmethod
    def build_cnf(args):
        return Roth(args.n, args.bound)


@register_cnf_generator
def Sidon(n, bound):
    F = CNF()

    def X(i):
        return "x_{{{0}}}".format(i)

    # Create variables
    for i in range(1, n+1):
        F.add_variable(X(i))

    # Conditions
    for i in range(1, n+1):
        for j in range(i, n+1):
            for k in range(i+1, n+1):
                for l in range(k, n+1):
                    if ((i+j) % n != (k+l) % n):
                        continue
                    x = {i, j, k, l}
                    F.add_clause([(False, X(q)) for q in x])

    if bound:
        F.add_greater_or_equal([X(i) for i in range(1, n+1)], bound)

    return F


@register_cnfgen_subcommand
class SidonCmdHelper(object):
    name = 'sidon'
    description = 'Sidon Set'

    @staticmethod
    def setup_command_line(parser):
        parser.add_argument('n', type=int)
        parser.add_argument('--bound', type=int)

    @staticmethod
    def build_cnf(args):
        return Sidon(args.n, args.bound)
