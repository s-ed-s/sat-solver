from solver.solver import SAT
import os

deciders = ["VSIDS"]


def run_tests(root_dir):
    for root, dirs, files in os.walk(root_dir):
        for dir_name in dirs:
            run_tests(root + "/" + dir_name)
        for filename in files:
            for decider in deciders:
                sat = SAT(False, decider)
                sat.solve(root + "/" + filename)
                sat.stats.print_stats()
        break


if __name__ == '__main__':
    run_tests("test")
