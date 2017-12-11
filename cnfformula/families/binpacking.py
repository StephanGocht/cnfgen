import cnfformula.cnf as cnf

import cnfformula.cmdline
import cnfformula.families

@cnfformula.families.register_cnf_generator
def BinPacking(numBins, binSize, items):
    r"""In the bein packing problem, objects of different volumes must be packed
    into a finite number of bins or containers each of volume V into a fixed
    number of bins.

    The encoding is equivalent to the following encoding:

    The variable :math:`x_{i,b}` encodes that item :math:`i` is in bin :math:`b`.

    Every item is in atleast one bin:

    .. math::
        \sum_{b \in \text{range}(\text{binSize})} x_{i,b} \geq 1
        \text{ for all } i \in \text{range}(|\text{items}|)

    Each bin has less items than its capacity:

    .. math::
        \sum_{i \in \text{range}(|\text{items}|)}
        \text{items}[i] \cdot x_{i,b} \leq \text{binSize}
        \text{ for all } b \in \text{range}(\text{numBins})



    Parameters
    ----------
    numBins : The number of bins encoded. asdf
    binSize : The size of the bins.
    items : A list that contains an entry for every item. The value is the
        size of the item.

    """


    F = cnf.CNF()
    F.header += "numBins: %d, binSize: %d \n" % (numBins, binSize)
    F.header += "items sizes: "
    F.header += ", ".join(map(str, items))
    F.header += "\n\n"

    for aBin in range(numBins):
        for item in range(len(items)):
            F.add_variable((item, aBin))

    def toArgs(listOfTuples, operator, degree):
        return list(sum(listOfTuples, ())) + [operator, degree]

    # Each item is in at leat one bin
    for item in range(len(items)):
        F.add_linear(
            *toArgs([(1, (item, aBin)) for aBin in range(numBins)],
                    ">=", 1
                )
        )

    # Each bin has no more than size items
    for aBin in range(numBins):
        F.add_linear(
            *toArgs([(items[i], (i, aBin)) for i in range(len(items))]
                ,"<=", binSize)
        )

    return F


@cnfformula.cmdline.register_cnfgen_subcommand
class BinPackingHelper(object):
    """Command line helper for the Clique-coclique CNF"""

    name='binpacking'
    description= """
        In the bin packing problem, objects of different volumes must be packed
        into a finite number of bins or containers each of volume V into a fixed
        number of bins.
        """

    @staticmethod
    def setup_command_line(parser):
        """Setup the command line options for clique-coloring formula

        Arguments:
        - `parser`: parser to load with options.
        """
        parser.description = BinPackingHelper.description
        parser.add_argument('numBins',type=int,help="Number of Bins.")
        parser.add_argument('binSize',type=int,help="Bin size.")
        parser.add_argument('item', metavar='size', type=int, nargs='*',
            help='Each number adds an item of the given size.')
        parser.add_argument(
            '-m', '--multiItem',
            metavar=('itemCount','itemSize'),
            help="Add itemCount items of size itemSize.",
            required=False, type=int, nargs=2, action='append')


    @staticmethod
    def build_cnf(args):
        """Build a bin packing formula

        Arguments:
        - `args`: command line options
        """
        items = args.item
        for item in args.multiItem:
            items += [item[1]] * item[0]
        return BinPacking(args.numBins, args.binSize, items)
