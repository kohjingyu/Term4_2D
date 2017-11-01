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
    public static Environment solve(Formula formula) {
        Environment env = new Environment();

        // long started = System.nanoTime();
        ImList<Clause> clauses = formula.getClauses(); //formula.sort(formula.getClauses());
        // System.out.println("Time taken: " + (System.nanoTime() - started));
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
    private static Environment solve(ImList<Clause> clauses, Environment env) {
        if(clauses.isEmpty()) {
            // No clauses, trivially satisfiable
            return env;
        }
        else {
            // Find smallest clause
            Clause smallest = clauses.first(); // Initialize as first Clause

            // remove empty clauses
            for(Clause c : clauses.rest()) {
                // if(c.isEmpty()) return null;

                if(c.size() < smallest.size()) {
                    smallest = c;
                }
            }

            // work on smallest clause
            // Pick arbitrary literal
            Literal first = smallest.chooseLiteral();
            Variable varToChange = first.getVariable();

            // Substitute for it
            ImList<Clause> newClauses = substitute(clauses, first);
            if(newClauses == null) {
                return null;
            }

            if(first instanceof NegLiteral) {
                // To set neg literal to true -> set variable to false
                env = env.put(varToChange, Bool.FALSE);
            }
            else {
                // To set pos literal to true -> set variable to true
                env = env.put(varToChange, Bool.TRUE);
            }

            Environment newSolution = solve(newClauses, env);
            
            if(newSolution != null || smallest.size() == 1) {
                return newSolution;
            }
            else {
                // If more than one literal, set to FALSE if the first one fails
                // Fails, substitute False and solve recursively
                if(first instanceof NegLiteral) {
                    // To set neg literal to false -> set var to true
                    env = env.put(varToChange, Bool.TRUE);
                }
                else {
                    // To set pos literal to false -> set var to false
                    env = env.put(varToChange, Bool.FALSE);
                }

                newClauses = substitute(clauses, first.getNegation());
                if(newClauses == null) {
                    return null;
                }

                return solve(newClauses, env);
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
