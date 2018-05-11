import json
import sys
from FAdo import rndfa 
# install FAdo from here
# http://fado.dcc.fc.up.pt/software/
# documentation
# http://www.dcc.fc.up.pt/~rvr/FAdo.pdf

'''
DFA (Q,\Sigma,i,F,\Delta) -> Regular Eqn

for each q \in Q:
    monomials = { l.q' | l \lin Sigma, (q,l,q') \in \Delta }
    if q in F:
        monomials += \epsilon
    add equation q = m_1 + ... m_n where m_i \in monomials
'''

def main():
    args = sys.argv
    if len(args) < 4:
        print "Usage: python gen.py <num_states> <num_symboles> <num_samples>\n"
        return -1
    num_states = int(args[1])
    num_symbols = int(args[2])
    num_samples = int(args[3])
    g = rndfa.ICDFArnd(num_states,num_symbols)
    count = 0
    test_cases = []
    while count < num_samples:
        d = g.next()
        if len(d.Final) == 0:
            pass
        else:
            count = count+1
            eqns = []
            for st in d.States:
                monomials = [ { 're': l, 'var': d.Delta(st,l)} for l in d.Sigma if d.Delta(st,l) is not None ]
                if st in d.Final:
                    monomials.append({ 're': 'eps'})
                eqn = { 'lhs':st, 'rhs' : monomials }
                eqns.append(eqn)
            test_cases.append(eqns)
    print json.dumps(test_cases)
    return 0

if __name__ == "__main__":
    sys.exit(main())


            
        

