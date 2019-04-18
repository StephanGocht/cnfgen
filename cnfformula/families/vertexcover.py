#!/usr/bin/env python
# -*- coding:utf-8 -*-

from cnfformula.cnf import CNF

from cnfformula.cmdline import SimpleGraphHelper

from cnfformula.cmdline import register_cnfgen_subcommand
from cnfformula.families import register_cnf_generator

from cnfformula.graphs import enumerate_vertices, neighbors


@register_cnf_generator
def VertexCover(G, d):
    F = CNF()

    def D(v):
        return "x_{{{0}}}".format(v)

    def N(v):
        return tuple(sorted([e for e in G.edges(v)]))

    # Fix the vertex order
    V = enumerate_vertices(G)

    # Create variables
    for v in V:
        F.add_variable(D(v))

    # Not too many true variables
    F.add_less_or_equal([D(v) for v in V], d)

    # Every edge must have a true D variable
    for e in G.edges():
        F.add_clause([(True, D(v)) for v in e])

    return F


@register_cnfgen_subcommand
class VertexCoverCmdHelper(object):
    """Command line helper for k-dominating set
    """
    name = 'vc'
    description = 'Vertex Cover'

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for dominating set formula

        Arguments:
        - `parser`: parser to load with options.
        """
        group = parser.add_mutually_exclusive_group(required=True)
        group.add_argument('--d', metavar='<d>', type=int,
                           action='store', help="size of the cover")
        group.add_argument('--rational', action='store_true',
                           help="Set size to V/2")
        group.add_argument(
            '--no-rational', action='store_true', help="Set size to V/2-1")
        SimpleGraphHelper.setup_command_line(parser)

    @staticmethod
    def build_cnf(args):
        """Build the k-dominating set formula

        Arguments:
        - `args`: command line options
        """
        G = SimpleGraphHelper.obtain_graph(args)
        D = args.d
        if args.rational:
            D = G.order()/2
        elif args.no_rational:
            D = G.order()/2-1
        return VertexCover(G, D)
