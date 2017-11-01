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

    public static HashMap<Variable, Bool> solve(Formula formula, int degree) {
        // 2SAT problem or lower - solve with SCC
        if(degree <= 2) {
            Graph graph = new Graph(formula);
            return graph.solve();
        }
        else {
            // Otherwise, solve with DPLL
            HashMap<Variable, Bool> env = new HashMap<Variable, Bool>();
            ImList<Clause> clauses = formula.getClauses();
            return solve(clauses, env);
        }
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

    public static HashMap<String, Bool> solveRandom(Formula formula, int numVariables, int degree) {
        // Find all variables
        if(degree <= 2) {
            HashMap<String, Bool> env = new HashMap<String, Bool>();
            long maxTries = 100L * numVariables * numVariables;
            return SATSolver.randomWalkify(formula, env, maxTries);
        }
        else {
            System.out.println("Not a 2SAT problem!");
            return null;
        }
    }

    public static HashMap<String, Bool> randomWalkify(Formula formula, HashMap<String, Bool> env, long triesLeft) {
        // If we exceed the number of tries, stop and return null (no answer found)
        while(triesLeft > 0)
        {
            // Find ONE unsatisfied clause
            Clause unsatClause = null;
            // ImList<Clause> clauses = new EmptyImList();
            for(Clause c: formula.getClauses()) {
                Iterator<Literal> litIter = c.iterator();
                Literal first = litIter.next();

                if(first != null) {
                    // Check if first literal is false - if so, check second literal
                    Variable firstVariable = first.getVariable();
                    Bool firstBool = env.get(firstVariable.getName());

                    if(first instanceof NegLiteral && firstBool != Bool.FALSE || first instanceof PosLiteral && firstBool != Bool.TRUE) {
                        // First not satisfied
                        Literal second = litIter.next();
                        if(second == null) {
                            // Clause not satisfied
                            unsatClause = c;
                            // clauses = clauses.add(c);
                            break; // break because we just need one unsatisfied clause
                        }
                        else {
                            Variable secondVariable = second.getVariable();
                            Bool secondBool = env.get(secondVariable.getName());

                            if(second instanceof NegLiteral && secondBool != Bool.FALSE || second instanceof PosLiteral && secondBool != Bool.TRUE) {
                                // Clause not satisfied
                                unsatClause = c;
                                // clauses = clauses.add(c);
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

            if(unsatClause == null) {
                // All clauses satisfied! Hooray!
                return env;
            }

            // Guarenteed to have at least one literal

            Iterator<Literal> litIter = unsatClause.iterator();
            Literal firstLit = litIter.next();
            Variable firstVar = firstLit.getVariable();
            Bool firstBool = env.get(firstVar.getName());

            Literal secondLit = litIter.next();
            Bool secondBool = null;
            Variable secondVar = null;

            if(secondLit != null)
            {
                secondVar = secondLit.getVariable();
                secondBool = env.get(secondVar.getName());

                if(secondBool == null) {
                    secondBool = Bool.FALSE;
                    env.put(secondVar.getName(), Bool.FALSE);
                }
            }

            if(firstBool == null) {
                firstBool = Bool.FALSE;
                env.put(firstVar.getName(), Bool.FALSE);
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

            // System.out.println(env);
            env.put(varToChange.getName(), boolToSet);
            // System.out.println(unsatClauses);
            // System.out.println(varToChange + " " + boolToSet);

            triesLeft -= 1;

            // return randomWalkify(formula, env, triesLeft - 1);

            // Iterator<Clause> clauseIter = formula.iterator();
            // Clause c = clauseIter.next();
            // while(c != null)
            // {

            //     c = clauseIter.next();
            // }
        }

        return null;
    }

}
