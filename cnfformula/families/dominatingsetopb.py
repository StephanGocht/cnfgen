#!/usr/bin/env python
# -*- coding:utf-8 -*-
"""Formulas that encode coloring related problems
"""

from cnfformula.cnf import CNF

from cnfformula.cmdline import SimpleGraphHelper

from cnfformula.cmdline  import register_cnfgen_subcommand
from cnfformula.families import register_cnf_generator

from cnfformula.graphs import enumerate_vertices,neighbors

@register_cnf_generator
def DominatingSetOPB(G,d,tiling,seed):
    F=CNF()

    def D(v):
        return "x_{{{0}}}".format(v)

    def N(v):
        return tuple(sorted([ v ] + [ u for u in G.neighbors(v) ]))

    # Fix the vertex order
    V=enumerate_vertices(G)

    #avgdegree=sum(len(set(N(v))) for v in V)/len(V)
    #d=len(V)/(avgdegree+1)
    
    # Create variables
    for v in V:
        F.add_variable(D(v))

    # Not too many true variables
    if not tiling:
        F.add_less_or_equal([D(v) for v in V],d)

    # Every neighborhood must have a true D variable
    neighborhoods = sorted( set(N(v) for v in V) )
    for N in neighborhoods:
        if tiling:
            F.add_equal_to([D(v) for v in N], 1)
        else:
            F.add_clause([(True,D(v)) for v in N])

    # Set some vertex to true
    if seed:
        F.add_clause([(True,D(V[0]))])
        
    return F

@register_cnfgen_subcommand
class DominatingSetCmdHelper(object):
    """Command line helper for k-dominating set
    """
    name='domsetopb'
    description='k-Dominating set'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for dominating set formula

        Arguments:
        - `parser`: parser to load with options.
        """
        group = parser.add_mutually_exclusive_group(required=True)
        group.add_argument('--d',metavar='<d>',type=int,action='store',help="size of the dominating set")
        group.add_argument('--regular',action='store_true',help="Set size to V/(deg+1)")
        group.add_argument('--tiling',action='store_true',help="Add tiling constraints")
        parser.add_argument('--seed',action='store_true',help="Set some vertex to true")
        SimpleGraphHelper.setup_command_line(parser)


    @staticmethod
    def build_cnf(args):
        """Build the k-dominating set formula

        Arguments:
        - `args`: command line options
        """
        G = SimpleGraphHelper.obtain_graph(args)
        D = args.d
        if args.regular : D = G.order()/(2*G.number_of_edges()/G.order()+1)
        return DominatingSetOPB(G, D, args.tiling, args.seed)
