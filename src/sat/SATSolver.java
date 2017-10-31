package sat;

import immutable.*;
import sat.env.Environment;
import sat.env.Bool;
import sat.env.Variable;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;
import sat.formula.NegLiteral;

import java.util.HashMap;
import java.util.ArrayList;
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
        Environment env = new Environment();

        return solve(formula.sort(formula.getClauses()), env);
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
            if(clauses.first().isEmpty()) return null;

            Clause smallest = clauses.first(); // Initialize as first Clause

            // Iterate through all the other Clauses
            for(Clause c : clauses.rest()) {
                // If this is an empty Clause, fail and backtrack
                if(c.isEmpty()) {
                    // Unsatisfiable, fail and backtrack
                    return null;
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

            }
            return trueEnv;
//            else {
//                // Works! Return
//                return trueEnv;
//            }
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

    public static Environment solveRandom(Formula formula, int numVariables) {
        // Find all variables
        Environment env = new Environment();

        // HashMap <Literal, ImList<Clause>> clauseMap = new HashMap<Literal, ImList<Clause>>();
        // ArrayList<Clause> unsatClauses = new ArrayList<Clause>();

        // for(Clause c: formula.getClauses())
        // {
        //     Iterator<Literal> litIter = c.iterator();
        //     Literal lit = litIter.next();
        //     boolean satisfied = false;

        //     while(lit != null) {
        //         env = env.putFalse(lit.getVariable());
        //         ImList<Clause> newClause = clauseMap.get(lit);

        //         if(newClause == null) {
        //             newClause = new EmptyImList<Clause>();
        //         }

        //         newClause = newClause.add(c);
        //         clauseMap.put(lit, newClause);

        //         // Since we default to false, negative literals are satisfied
        //         if(lit instanceof NegLiteral) {
        //             satisfied = true;
        //         }

        //         lit = litIter.next();
        //     }

        //     if(satisfied) {
        //         unsatClauses.add(c);
        //     }
        // }

        long maxTries = 100 * numVariables * numVariables;
        return SATSolver.randomWalkify(formula, env, maxTries);
    }

    public static Environment randomWalkify(Formula formula, Environment env, long triesLeft) {
        // If we exceed the number of tries, stop and return null (no answer found)
        if(triesLeft <= 0) {
            return null;
        }

        // Find unsatisfied clauses
        ImList<Clause> unsatClauses = formula.getClauses();
        for(Clause c: unsatClauses) {
            Iterator<Literal> litIter = c.iterator();
            Literal f = litIter.next();

            if(f != null) {

            }
            else {
                // Empty clause - unsolvable
                return null;
            }
        }

        // Find unsatisfied clauses
        ImList<Clause> clauses = unsatClauses; // TODO: Remove
        Clause c = clauses.first(); // Guarenteed to have at least one literal

        Iterator<Literal> litIter = c.iterator();
        if(clauses.size() == 0) {
            // All clauses satisfied! Hooray!
            return env;
        }

        Literal firstLit = litIter.next();

        Variable firstVar = firstLit.getVariable();
        Bool firstBool = firstVar.eval(env);

        Literal secondLit = litIter.next();

        Bool secondBool = Bool.FALSE;
        Variable secondVar = null;

        if(secondLit != null)
        {
            secondVar = secondLit.getVariable();
            secondBool = secondVar.eval(env);
        }

        // If it is a negative literal, evaluate it using the NegLiteral's eval method instead
        if(firstLit instanceof NegLiteral) {
            firstBool = ((NegLiteral)firstLit).eval(env);
        }

        if(firstBool == Bool.UNDEFINED) {
            firstBool = Bool.FALSE;
            env = env.put(firstVar, Bool.FALSE);
        }

        if(secondLit instanceof NegLiteral) {
            secondBool = ((NegLiteral)secondLit).eval(env);
        }

        if(secondBool == Bool.UNDEFINED) {
            secondBool = Bool.FALSE;
            env = env.put(secondVar, Bool.FALSE);
        }

        // Unsatisfied clause - change one variable randomly
        Variable varToChange = firstVar;
        Literal literalToChange = firstLit;
        Bool boolToSet = firstBool.not();

        // If this Clause has 2 variables, pick one at random to change
        if(secondLit != null) {
            Random rand = new Random();
            int randNum = rand.nextInt(2);

            if(randNum == 1) {
                varToChange = secondVar;
                literalToChange = secondLit;
                boolToSet = secondBool.not();
            }
        }

        return randomWalkify(formula, env, triesLeft - 1);

        // Iterator<Clause> clauseIter = formula.iterator();
        // Clause c = clauseIter.next();
        // while(c != null)
        // {

        //     c = clauseIter.next();
        // }
    }

}
