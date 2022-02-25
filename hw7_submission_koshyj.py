import random
import numpy as np
import signal, datetime
import argparse
import copy
import json
import time
import math
'''
homework 7 - koshyj testing suite
check for dpll and hillclimb alg
'''
class TimeoutException(Exception):
    pass

def handle_maxSeconds(signum, frame):
    raise TimeoutException()

VERBOSE=True

# return True if clause has a true literal
def check_clause(clause, assignment):
    clause_val = False
    for i in clause:
        if np.sign(i)==np.sign(assignment[abs(i)-1]): #assignment is 0-ref, variables 1-ref
                clause_val=True
    return clause_val

def check(clauses,assignment):
    global VERBOSE
    
    if VERBOSE:
        print('Checking assignment {}'.format(assignment))
        print('score of assignment is {}'.format(score(clauses,assignment)))
    for clause in clauses:
        if not check_clause(clause, assignment):
            return clause
    print('Check succeeded!')
    return True

# calculate given score to check redundant values against the clause and given assigments.
def score(clauses, assignment):
    sum = 0
    for clause in clauses:
        if check_clause(clause, assignment):
            sum += 1
    return sum

# find random value for set in next state actions on algorithm
def get_random(clauses, num_variables):
    range_set = 100
    score = []
    state = []
    for x in range(range_set):
        set_range = [random.randint(0, 1) - 1 for _ in range(num_variables)]
        state.append(np.array(set_range))
        score.append(score(clauses, state[x]))
    max_score = max(score)
    start_state = state[score.index(max_score)]
    return start_state

# hill climb algorithm that works efficiently with some added optimizations. First check is that random start given numvariables and clauses that are accesible to be used.
# The algorithm then continues down and makes a check for the best score possible while lookng through that start state, a new state is chosen every time a solution is not followed or made.
# This will then find the solution after the check has been made for best case.
def simple_hillclimb(clauses, num_variables):
    if clauses == None:
        return False
        
    assignment = get_random(clauses, num_variables)
    breakpoint = 1

    while (breakpoint):
        main_check = check(clauses, assignment)
        if breakpoint == main_check:
            break

        score = [0] * num_variables
        for x in range(num_variables):
            assignment[x] *= -1
            score[x] = score(clauses, assignment)
            assignment[x] *= -1
            max_score = max(score)
        next_state = score.index(max_score)

        if score[next_state] <= score(clauses, assignment):
            assignment = get_random(clauses, num_variables)
        else:
            assignment[next_state] *= -1    

    if assignment == None:
        return False

    return assignment
       
def backtrack_search (num_variables, clauses):
    print('Backtracking search started')

    def backtrack(assignment,i):
        # i is next variable number to try values for (1..numvariables)
        if i==num_variables+1:  # no more variables to try
            if check(clauses,assignment)==True:
                return assignment
            return None
        else:
            for val in [-1,1]:
                assignment[i-1]=val  # assignment is 0-ref, so assignment[x] stores variable x+1 value
                result=backtrack(assignment,i+1)
                if result != None:
                    return result
        return None

    assignment = np.array([1]*num_variables)
    result=backtrack(assignment,1)
    print('Backtracking search completed successfully')
    return(result)

def random_walk(num_variables, clauses):
    print('Random walk search started')
    assignment = np.ones(num_variables)
    while True:
        if True==check(clauses,assignment):
            break
        var_to_flip=random.randint(1,num_variables)
        assignment[var_to_flip-1] *= -1
    print('Random walk search completed successfully')
    return assignment

# Flip more than one variable at a time
def generate_solvable_problem(num_variables): 
    global VERBOSE
    
    k=3 # 3-SAT
    random.seed()
    
    clauses_per_variable = 4.2  # < 4.2 easy;  >4.2 usually unsolvable.  4.2 challenging to determine.
    num_clauses=round(clauses_per_variable*num_variables)

    # this assignment will solve the problem
    target = np.array([2*random.randint(0,1)-1 for _ in range(num_variables)]) 
    clauses=[]
    for i in range(num_clauses):
        seeking = True
        while seeking:
            clause=sorted((random.sample(range(0,num_variables),k))) # choose k variables at random 
            clause=[i+1 for i in clause]
            clause=[(2*random.randint(0,1)-1)*clause[x] for x in range(k)] # choose their signs at random
            seeking = not check_clause(clause,target)
        clauses.append(clause)

    if VERBOSE:
        print('Problem is {}'.format(clauses))
        print('One solution is {} which checks to {}'.format(target,check(clauses,target)))
        
    return clauses

def hw7_submission(num_variables, clauses, timeout):  #timeout is provided in case your method wants to know
    return simple_hillclimb(clauses, num_variables)

def solve_SAT(file,save,timeout,num_variables,algorithms,verbose):
    global VERBOSE
    
    VERBOSE=verbose

    if file != None:
        with open(file,"r") as f:
            [num_variables,timeout,clauses] = json.load(f)
        print('Problem with {} variables and timeout {} seconds loaded'.format(num_variables,timeout))
    else:
        clauses = generate_solvable_problem(num_variables)
        if timeout==None:
            timeout = round(60 * num_variables / 100)
        print('Problem with {} variables generated, timeout is {}'.format(num_variables,timeout))

    if save != None:
        with open(save,"w") as f:
            json.dump((num_variables,timeout,clauses),f)

    if 'hw7_submission' in algorithms:
        signal.signal(signal.SIGALRM, handle_maxSeconds)
        signal.alarm(timeout)
        startTime = datetime.datetime.now()
        try:
            result="Timeout"
            result=hw7_submission(num_variables,clauses,timeout)
            print('Solution found is {}'.format(result))
            if not (True == check(clauses,result)):
                print('Returned assignment incorrect')
        except TimeoutException:
            print("Timeout!")
        endTime = datetime.datetime.now()
        seconds_used = (endTime - startTime).seconds
        signal.alarm(0)
        print('Search returned in {} seconds\n'.format(seconds_used))
    if 'backtrack' in algorithms:
        signal.signal(signal.SIGALRM, handle_maxSeconds)
        signal.alarm(timeout)
        startTime = datetime.datetime.now()
        try:
            result="Timeout"
            result=backtrack_search(num_variables,clauses)
            print('Solution found is {}'.format(result))
            if not (True == check(clauses,result)):
                print('Returned assignment incorrect')
        except TimeoutException:
            print("Timeout!")
        endTime = datetime.datetime.now()
        seconds_used = (endTime - startTime).seconds
        signal.alarm(0)
        print('Search returned in {} seconds\n'.format(seconds_used))
    if 'random_walk' in algorithms:
        signal.signal(signal.SIGALRM, handle_maxSeconds)
        signal.alarm(timeout)
        startTime = datetime.datetime.now()
        try:
            result="Timeout"
            result=random_walk(num_variables,clauses)
            print('Solution found is {}'.format(result))
            if not (True == check(clauses,result)):
                print('Returned assignment incorrect')
        except TimeoutException:
            print("Timeout!")
        endTime = datetime.datetime.now()
        seconds_used = (endTime - startTime).seconds
        signal.alarm(0)
        print('Search returned in {} seconds\n'.format(seconds_used))

def main():
    parser = argparse.ArgumentParser(description="Run stochastic search on a 3-SAT problem")
    parser.add_argument("algorithms", nargs='*',
                        help="Algorithms to try",
                        choices=['random_walk' , 'hw7_submission', 'backtrack'])
    parser.add_argument("-f", "--file", help="file name with 3-SAT formula to use", default=None)
    parser.add_argument("-s", "--save", help="file name to save problem in", default=None)
    parser.add_argument("-t", "--timeout", help="Seconds to allow (default based on # of vars)", type=int, default=None)
    parser.add_argument("-n", "--numvars", help="Number of variables (default 20)", type=int, default=20)
    parser.add_argument("-v", "--verbose", help="Whether to print tracing information", action="store_true")
    
    args = parser.parse_args()
    file = args.file
    save = args.save
    timeout = args.timeout
    num_variables = args.numvars 
    algorithms = args.algorithms
    verbose = args.verbose

    if (file!=None and (timeout != None or num_variables != None)):
        print('\nUsing input file, any command line parameters for number of variables and timeout will be ignored\n')
    solve_SAT(file,save,timeout,num_variables,algorithms,verbose)

if __name__ == '__main__':
    main()



# if you prefer to load the file rather than use command line
# parameters, use this section to configure the solver
#
# outfile = None # 'foo.txt'
# infile  = None # 'save500.txt'
# timeout = None #ignored if infile is present, will be set based on numvars if None here
# numvars = 70   #ignored if infile is present
# algorithms = ['random_walk', 'backtrack', 'hw7_submission']
# verbosity = False
# solve_SAT(infile, outfile, timeout, numvars, algorithms, verbosity)
