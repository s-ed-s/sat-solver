import argparse
from solver.solver import SAT

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description='Reads a file and try to determine satisfiability by CDCL.'
        ' Example usage: python main.py -p test/test1.cnf'
    )
    parser.add_argument(
        '-l',
        '--log',
        help='logging value (True or False), default = False',
        default=False
    )
    parser.add_argument(
        '-d',
        '--decider',
        default="VSIDS",
        help='Decision Heuristic to be used (VSIDS or ORDERED)'
    )
    parser.add_argument(
        '-p',
        '--path',
        required=True,
        type=str,
        nargs='?',
        help='path of .cnf file'
    )
    args = parser.parse_args()

    is_log = args.log
    decider = args.decider
    path = args.path

    if is_log not in [True, False]:
        raise ValueError("The logging argument should be either True or False.")
    if decider not in ["VSIDS", "ORDERED"]:
        raise ValueError("The decider argument should be either VSIDS or ORDERED.")

    sat = SAT(is_log, decider)
    sat.solve(path)
    sat.stats.print_stats()