# sat-solver
A SAT Solver based on CDCL (Conflict Driven Clause Learning) implemented in Python.

The solvers currently only accepts CNF files in DIMACS format and return dictionary of variable to its assigned boolean value.
## run
```commandline
main.py [-l LOG] [-d DECIDER] -p [PATH]
```
where LOG must be True or False (default=False), decider must be ORDERED or VSIDS (default=VSIDS), PATH is valid path to the DIMACS CNF input file.

Example
```commandline
python main.py -p test/test1.cnf
```
To run all the tests, you can use the command
```commandline
python run_all_tests.py
```