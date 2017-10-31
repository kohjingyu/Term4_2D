package sat;

import immutable.ImList;
import sat.env.Environment;
import sat.env.Bool;
import sat.env.Variable;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;
import sat.formula.PosLiteral;
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
        // TODO: implement this.
        System.out.println(formula);

        throw new RuntimeException("not yet implemented.");
    }

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
        // TODO: implement this.
        throw new RuntimeException("not yet implemented.");
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
        // TODO: implement this.
        throw new RuntimeException("not yet implemented.");
    }

}
