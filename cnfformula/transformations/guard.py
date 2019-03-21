#!/usr/bin/env python
# -*- coding:utf-8 -*-

import random

from ..cmdline  import register_cnf_transformation_subcommand
from ..transformations import register_cnf_transformation

from ..cnf import CNF, disj, xor, less, greater, geq, leq


@register_cnf_transformation
def Guard(cnf):
    """Guard clauses with spoiler literals.

    Makes a formula harder for regular resolution. Examples of inputs
    for which this works:

    * Ordering principle [AJPU07].
    * Xorified pebbling [Urq11].

    """

    out=CNF()
    out._header="Guarded formula\n\n"+cnf._header

    for v in cnf.variables():
        out.add_variable(v)

    variables = range(1, len(list(cnf.variables())) + 1)

    # build and add new clauses
    for orig_cnst in cnf._constraints:
        for orig_cls in orig_cnst.clauses():
            extra_var = random.choice(variables)
            if extra_var in orig_cls or -extra_var in orig_cls:
                out._add_compressed_constraints([orig_cls])
            else:
                new_cls = [disj(*(orig_cls + (extra_var,))),
                           disj(*(orig_cls + (-extra_var,)))]
                out._add_compressed_constraints(new_cls)

    out._check_coherence()

    # return the formula
    return out


@register_cnf_transformation_subcommand
class GuardCmd:
    """Guard clauses
    """
    name='guard'
    description='Guard clauses with spoiler literals'

    @staticmethod
    def setup_command_line(parser):
        pass

    @staticmethod
    def transform_cnf(F, args):
        return Guard(F)
