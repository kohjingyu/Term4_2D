package sat;

import immutable.*;
import sat.env.Environment;
import sat.env.Bool;
import sat.env.Variable;
import sat.formula.*;

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
    public static HashMap<Variable, Bool> solve(Formula formula) {
        HashMap<Variable, Bool> env = new HashMap<Variable, Bool>();
        ImList<Clause> clauses = formula.getClauses();
        return solve(clauses, env);
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
    private static HashMap<Variable, Bool> solve(ImList<Clause> clauses, HashMap<Variable, Bool> env) {
        if(clauses.isEmpty()) {
            // No clauses, trivially satisfiable
            return env;
        }
        else {
            // Find smallest clause
            Clause smallest = clauses.first(); // Initialize as first Clause
            for(Clause c : clauses.rest()) {
                if(c.size() < smallest.size()) {
                    smallest = c;
                }
            }

            // Work on smallest clause
            // Pick arbitrary literal

            Literal first = smallest.chooseLiteral();
            Variable varToChange = first.getVariable();
            ImList<Clause> newClauses = substitute(clauses, first);
            // substitute returns null if there's an empty Clause (unsatisfiable)
            if(newClauses == null) {
                return null;
            }

            if(first instanceof NegLiteral) {
                // To set neg literal to true -> set variable to false
                env.put(varToChange, Bool.FALSE);
            }
            else {
                // To set pos literal to true -> set variable to true
                env.put(varToChange, Bool.TRUE);
            }

            if(smallest.size() == 1) {
                // Substitute for it
                return solve(newClauses, env);
            }
            else {
                // Substitute for it
                HashMap<Variable, Bool> firstSol = solve(newClauses, env);

                if(firstSol == null) {
                    newClauses = substitute(clauses, first.getNegation());
                    // substitute returns null if there's an empty Clause (unsatisfiable)
                    if(newClauses == null) {
                        return null;
                    }

                    if(first instanceof NegLiteral) {
                        // To set neg literal to true -> set variable to false
                        env.put(varToChange, Bool.TRUE);
                    }
                    else {
                        // To set pos literal to true -> set variable to true
                        env.put(varToChange, Bool.FALSE);
                    }

                    return solve(newClauses, env);
                }
                else {
                    return firstSol;
                }
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
            if(c.contains(l) || c.contains(l.getNegation())) {
                Clause reducedC = c.reduce(l);
                if(reducedC != null) {
                    if(reducedC.isEmpty()) {
                        return null;
                    }

                    newClauses = newClauses.add(reducedC);
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
        long maxTries = 100L * numVariables * numVariables;
        System.out.println(maxTries);
        return SATSolver.randomWalkify(formula, env, maxTries);
    }

    public static Environment randomWalkify(Formula formula, Environment env, long triesLeft) {
        // If we exceed the number of tries, stop and return null (no answer found)
        System.out.println(triesLeft);
        if(triesLeft <= 0) {
            return null;
        }

        // Find ONE unsatisfied clause
        ImList<Clause> unsatClauses = new EmptyImList();
        for(Clause c: formula.getClauses()) {
            Iterator<Literal> litIter = c.iterator();
            Literal f = litIter.next();

            if(f != null) {
                // Check if first literal is false - if so, check second literal
                Bool firstBool = f.getVariable().eval(env);

                if(f instanceof NegLiteral && firstBool != Bool.FALSE || f instanceof PosLiteral && firstBool != Bool.TRUE) {
                    // First not satisfied
                    Literal second = litIter.next();
                    if(second == null) {
                        // Clause not satisfied
                        unsatClauses = unsatClauses.add(c);
                        break; // break because we just need one unsatisfied clause
                    }
                    else {
                        Bool secondBool = second.getVariable().eval(env);
                        if(second instanceof NegLiteral && secondBool != Bool.FALSE || second instanceof PosLiteral && secondBool != Bool.TRUE) {
                            // Clause not satisfied
                            unsatClauses = unsatClauses.add(c);
                            break; // break because we just need one unsatisfied clause
                        }
                    }
                }
            }
            else {
                // Empty clause - unsolvable
                return null;
            }
        }

        System.out.println(unsatClauses);

        // Find unsatisfied clauses
        ImList<Clause> clauses = unsatClauses; // TODO: Remove
        if(clauses.size() == 0) {
            // All clauses satisfied! Hooray!
            return env;
        }

        Clause c = clauses.first(); // Guarenteed to have at least one literal

        Iterator<Literal> litIter = c.iterator();
        Literal firstLit = litIter.next();
        Variable firstVar = firstLit.getVariable();
        Bool firstBool = firstVar.eval(env);

        Literal secondLit = litIter.next();
        Bool secondBool = null;
        Variable secondVar = null;

        if(secondLit != null)
        {
            secondVar = secondLit.getVariable();
            secondBool = secondVar.eval(env);
        }

        if(firstBool == Bool.UNDEFINED) {
            firstBool = Bool.FALSE;
            env = env.put(firstVar, Bool.FALSE);
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

        env = env.put(varToChange, boolToSet);
        // System.out.println(unsatClauses);
        // System.out.println(varToChange + " " + boolToSet);

        return randomWalkify(formula, env, triesLeft - 1);

        // Iterator<Clause> clauseIter = formula.iterator();
        // Clause c = clauseIter.next();
        // while(c != null)
        // {

        //     c = clauseIter.next();
        // }
    }

}
