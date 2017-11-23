#!/usr/bin/env python
# -*- coding:utf-8 -*-
"""Implementation of Tseitin formulas
"""

from cnfformula.cnf import CNF

from cnfformula.cmdline import SimpleGraphHelper
from cnfformula.graphs import enumerate_vertices,neighbors

import random
import cnfformula.cmdline
import cnfformula.families

@cnfformula.families.register_cnf_generator
def TseitinFormula(graph,charges=None, encoding=None):
    """Build a Tseitin formula based on the input graph.

    Odd charge is put on the first vertex by default, unless other
    vertices are is specified in input.

    Arguments:
    - `graph`: input graph
    - `charges': odd or even charge for each vertex
    """
    V=enumerate_vertices(graph)

    if charges==None:
        charges=[1]+[0]*(len(V)-1)             # odd charge on first vertex
    else:
        charges = [bool(c) for c in charges]   # map to boolean

    if len(charges)<len(V):
        charges=charges+[0]*(len(V)-len(charges))  # pad with even charges
        assert False

    # init formula
    tse=CNF()
    edgename = { }

    for (u,v) in sorted(graph.edges(),key=sorted):
        edgename[(u,v)] =  "E_{{{0},{1}}}".format(u,v)
        edgename[(v,u)] =  "E_{{{0},{1}}}".format(u,v)
        tse.add_variable(edgename[(u,v)])

    tse.mode_strict()
    # add constraints
    for v,charge in zip(V,charges):

        # produce all clauses and save half of them
        names = [ edgename[(u,v)] for u in neighbors(graph,v) ]
        if encoding == None:
            tse.add_parity(names,charge)
        elif encoding == "extendedPBAnyHelper":
            def toArgs(listOfTuples, operator, degree):
                return list(sum(listOfTuples, ())) + [operator, degree]

            terms = list(map(lambda x: (1, x), names))
            w = len(terms)
            k = w // 2
            for i in range(k):
                helper = ("xor_helper", i)
                tse.add_variable(helper)
                terms.append((2, helper))
            degree = 2 * k + (charge % 2)
            tse.add_linear(*toArgs(terms, "==", degree))

    return tse


@cnfformula.cmdline.register_cnfgen_subcommand
class TseitinCmdHelper(object):
    """Command line helper for Tseitin  formulas
    """
    name='tseitin'
    description='tseitin formula'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for Tseitin formula

        Arguments:
        - `parser`: parser to load with options.
        """
        parser.add_argument('--charge',metavar='<charge>',default='first',
                            choices=['first','random','randomodd','randomeven', '0','1'],
                            help="""charge on the vertices.
                                    `first'  puts odd charge on first vertex;
                                    `random' puts a random charge on vertices;
                                    `randomodd' puts random odd  charge on vertices;
                                    `randomeven' puts random even charge on vertices.
                                     """)
        group = parser.add_mutually_exclusive_group()
        group.add_argument("--extendedPBAnyHelper", action='store_true',
            help="Encode xor as pseudo boolean constraint with extended variables.")

        SimpleGraphHelper.setup_command_line(parser)

    @staticmethod
    def build_cnf(args):
        """Build Tseitin formula according to the arguments

        Arguments:
        - `args`: command line options
        """
        G = SimpleGraphHelper.obtain_graph(args)

        if G.order()<1:
            charge=None

        elif args.charge=='first':

            charge=[1]+[0]*(G.order()-1)

        elif args.charge in ['0', '1']:
            charge = [int(args.charge)] * G.number_of_nodes()

        else: # random vector
            charge=[random.randint(0,1) for _ in range(G.order()-1)]

            parity=sum(charge) % 2

            if args.charge=='random':
                charge.append(random.randint(0,1))
            elif args.charge=='randomodd':
                charge.append(1-parity)
            elif args.charge=='randomeven':
                charge.append(parity)
            else:
                raise ValueError('Illegal charge specification on command line')

        encoding = None
        if args.extendedPBAnyHelper:
            encoding = "extendedPBAnyHelper"

        return TseitinFormula(G, charge, encoding)
