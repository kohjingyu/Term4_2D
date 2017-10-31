package sat;

import immutable.ImList;
import sat.env.Environment;
import sat.env.Bool;
import sat.env.Variable;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;
import sat.formula.NegLiteral;

import java.util.Iterator;
import java.util.Random;

/**
 * A simple DPLL SAT solver. See http://en.wikipedia.org/wiki/DPLL_algorithm
 */
public class SATSolver {

    /**
     * Solve the problem using a simple version of DPLL with backtracking and
     * unit propagation. The returned environment binds literals of class
     * bool.Variable rather than the special literals used in clausification of
     * class clausal.Literal, so that clients can more readily use it.
     * 
     * @return an environment for which the problem evaluates to Bool.TRUE, or
     *         null if no such environment exists.
     */
    public static Environment solve(Formula formula) {
        // Initially use an environment where everything is true
        Environment env = new Environment();
        return solve(formula.getClauses(), env);
    }

    /**
     * Takes a partial assignment of variables to values, and recursively
     * searches for a complete satisfying assignment.
     * 
     * @param clauses
     *            formula in conjunctive normal form
     * @param env
     *            assignment of some or all variables in clauses to true or
     *            false values.
     * @return an environment for which all the clauses evaluate to Bool.TRUE,
     *         or null if no such environment exists.
     */
    private static Environment solve(ImList<Clause> clauses, Environment env) {
        if(clauses.isEmpty()) {
            // No clauses, trivially satisfiable
            return env;
        }
        else {
            // Find smallest clause
            Clause smallest = clauses.first(); // Initialize as first Clause

            if(smallest.isEmpty()) return null;

            // Iterate through all the other Clauses
            for(Clause c : clauses.rest()) {
                // If this is an empty Clause, fail and backtrack
                if(c.isEmpty()) {
                    // Unsatisfiable, fail and backtrack
                    return null;
                }
                // Check if this Clause is smaller
                else if(c.size() < smallest.size()) {
                    // Set this to be the smallest
                    smallest = c;
                }
            }

            // work on smallest clause
            // Pick arbitrary literal
            Literal l = smallest.chooseLiteral();
            Variable varToChange = l.getVariable();
            Bool boolToSet = Bool.TRUE;

            // If it is a negative literal, evaluate it using the NegLiteral's eval method instead
            if(l instanceof NegLiteral) {
                boolToSet = ((NegLiteral)l).eval(env);

                if(boolToSet == Bool.UNDEFINED) {
                    boolToSet = Bool.TRUE;
                }
            }

            // Substitute for it
            ImList<Clause> newClauses = substitute(clauses, l);
            Environment newEnv = env.put(varToChange, boolToSet);
            Environment trueEnv = solve(newClauses, newEnv);

            if(trueEnv == null && clauses.size() > 1) {
                // Fails, substitute False and solve recursively
                newClauses = substitute(clauses, l.getNegation());
                newEnv = env.put(varToChange, boolToSet.not());
                return solve(newClauses, newEnv);
            }
            else {
                // Works! Return
                return trueEnv;
            }
        }
    }

    /**
     * given a clause list and literal, produce a new list resulting from
     * setting that literal to true
     * 
     * @param clauses
     *            , a list of clauses
     * @param l
     *            , a literal to set to true
     * @return a new list of clauses resulting from setting l to true
     */
    private static ImList<Clause> substitute(ImList<Clause> clauses,
            Literal l) {
        ImList<Clause> newClauses = clauses;

        for (Clause c : clauses) {
            // c is single variable clause
            if (c.contains(l)){
                if(c.reduce(l) != null) {
                    newClauses = newClauses.add(c.reduce(l));
                }
                newClauses = newClauses.remove(c);
            }
        }
        return newClauses;
    }

    /**
    * Solve the problem by taking a random walk in 2D. Not guarenteed to produce a correct answer,
    * but usually does with high probability. Performs 100n^2 tries before giving up.
    **/

    public static Environment solveRandom(Formula formula) {
        // Find all variables
        Environment env = new Environment();        

        Iterator<Clause> clauseIter = formula.iterator();
        Clause c = clauseIter.next();
        while(c != null)
        {
            Iterator<Literal> litIter = c.iterator();
            Literal lit = litIter.next();
            while(lit != null) {
                env = env.putFalse(lit.getVariable());
                lit = litIter.next();
            }
            c = clauseIter.next();
        }

        // System.out.println(env);
        int maxTries = 100 * env.getSize() * env.getSize();
        return SATSolver.randomWalkify(formula, env, maxTries);
    }

    public static Environment randomWalkify(Formula formula, Environment env, int triesLeft) {
        // If we exceed the number of tries, stop and return null (no answer found)
        if(triesLeft <= 0) {
            return null;
        }
        
        // Find unsatisfied clauses
        Iterator<Clause> clauseIter = formula.iterator();
        Clause c = clauseIter.next();
        while(c != null)
        {
            // Check if clause is satisfied
            Iterator<Literal> litIter = c.iterator();
            Literal firstLit = litIter.next();
            Literal secondLit = litIter.next();
            Variable firstVar = firstLit.getVariable();
            Variable secondVar = secondLit.getVariable();
            Bool firstBool = firstVar.eval(env);
            Bool secondBool = secondVar.eval(env);

            // If it is a negative literal, evaluate it using the NegLiteral's eval method instead
            if(firstLit instanceof NegLiteral) {
                firstBool = ((NegLiteral)firstLit).eval(env);
            }

            if(secondLit instanceof NegLiteral) {
                secondBool = ((NegLiteral)secondLit).eval(env);
            }

            if(firstBool.or(secondBool) == Bool.TRUE) {
                // Clause is satisfied, move on
            }
            else {
                // Unsatisfied clause - change one variable randomly
                Variable varToChange = firstVar;

                // If this Clause has 2 variables, pick one at random to change
                if(secondLit != null) {
                    Random rand = new Random();
                    int randNum = rand.nextInt(2);

                    if(randNum == 1) {
                        varToChange = secondVar;
                    }
                }

                // Try again with the new variable
                Environment newEnv = env.put(varToChange, firstBool.not());
                return randomWalkify(formula, newEnv, triesLeft - 1);
            }

            c = clauseIter.next();
        }

        // All clauses satisfied! Hooray!
        return env;
    }

}
