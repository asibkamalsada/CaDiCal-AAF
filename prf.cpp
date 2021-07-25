/*
MIT License

Copyright (c) 2021 Asib Kamalsada

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
 */

#include <algorithm>
//
// Created by asib1 on 12.03.2021.
//

#include "cadical.hpp"
#include <string>
#include <fstream>
#include <iostream>
#include <unordered_map>

using namespace std;

#define DEBUG 0

// if debug print to console
#define LOG(S) if (DEBUG) cout << S

// log and add to solver
#define ADD(X) LOG(X); solver->add(X)

#define SPACE LOG(' ')
#define NL LOG('\n')

// log, add and log a space
#define ADD_S(X) ADD(X); SPACE
// terminate the clause and log a new line
#define TERM_CL ADD(0); NL

int main(__unused int argc, char *argv[]) {
    auto *solver = new CaDiCaL::Solver;
    solver->set("quiet", 1);

    // translate an argument to a literal
    unordered_map<std::string, int> arg2lit;
    // translate a literal to an argument
    unordered_map<int, std::string> lit2arg;

#define B_SIZE 20

    // buffer for reading in an argument
    char b[B_SIZE];

    // character read from file
    char ch;
    // input stream
    fstream fin(argv[1], fstream::in);

    // total number of arguments
    int argcount = 0;

    bool args_finished = false;

    // the amount of predecessors (attackers) of an argument
    int *pre_counts;

    // the actual predecessors (attackers) of an argument
    unordered_map<int, int *> pre;

    // read one character at a time
    while (fin >> noskipws >> ch) {
        if (ch == 'a') {
            fin >> noskipws >> ch;
            if (ch == 'r') {
                fin >> noskipws >> ch;
                if (ch == 'g') {
                    fin >> noskipws >> ch;
                    if (ch == '(') {
                        // at this point, an argument is expected
                        fin >> noskipws >> ch;
                        unsigned int counter = 0;
                        // read the argument name which is delimited by a closing parenthesis
                        while (ch != ')') {
                            if (counter > B_SIZE) exit(1);
                            b[counter] = ch;
                            fin >> noskipws >> ch;
                            counter++;
                        }
                        argcount++;
                        // convert the buffered argument name to a string
                        std::string s(b, counter);
                        // the n-th argument is represented by the literal n
                        arg2lit[s] = argcount;
                        lit2arg[argcount] = s;
                    }
                }
            } else if (ch == 't') {
                fin >> noskipws >> ch;
                if (ch == 't') {
                    fin >> noskipws >> ch;
                    if (ch == '(') {
                        // at this point, an attack is expected

                        // if this is the first attack
                        if (!args_finished) {
                            args_finished = true;
                            solver->reserve(argcount);
                            // allocate memory and initialize arrays for pre
                            pre_counts = (int *) calloc(argcount, sizeof(int));
                            for (int i = 0; i < argcount; i++) {
                                pre[i] = new int[argcount];
                            }
                            LOG("conflictfree\n");
                        }
                        // conflictfree
                        int lit1;
                        int lit2;
                        fin >> noskipws >> ch;
                        unsigned int counter = 0;
                        // read first argument
                        while (ch != ',') {
                            if (counter > B_SIZE) exit(1);
                            b[counter] = ch;
                            fin >> noskipws >> ch;
                            counter++;
                        }
                        lit1 = arg2lit[std::string(b, counter)];

                        fin >> noskipws >> ch;
                        counter = 0;
                        // read second argument
                        while (ch != ')') {
                            if (counter > B_SIZE) exit(1);
                            b[counter] = ch;
                            fin >> noskipws >> ch;
                            counter++;
                        }
                        lit2 = arg2lit[std::string(b, counter)];

                        // e.g.
                        // att(a,b)
                        // leads to adding
                        // NOT(a) OR NOT(b)
                        // to the solver. Ensures conflictfree
                        ADD_S(-lit1);
                        ADD_S(-lit2);
                        TERM_CL;

                        // adding lit1 as an attacker of lit2
                        pre[lit2 - 1][pre_counts[lit2 - 1]] = lit1;
                        pre_counts[lit2 - 1]++;

                    }
                }
            }
        }
    }

// attacker literal
#define ATT pre[i][pre_count]
// attacker index
#define ATT_I ATT - 1

    for (int i = 0; i < argcount; i++) {
#       define loop_lit (i + 1)
        // admissible
        for (int pre_count = 0; pre_count < pre_counts[i]; pre_count++) {
            LOG("adm ");
            for (int pre_pre_count = 0; pre_pre_count < pre_counts[ATT_I]; pre_pre_count++) {
                // add every attacker of an attacker of the argument
                ADD_S(pre[ATT_I][pre_pre_count]);
            }
            // add the argument itself but negated
            ADD_S(-(loop_lit));
            TERM_CL;
        }
    }

    // buffers exactly one solution by saving the signed literals of the model of the solver
    int sol_buff[argcount];

    cout << "[\n" << flush;

    // while there are solutions
    while (solver->solve() == 10) {

        // after one execution of this body a single preferred solution has to be found

        int res;
        do {
            // copy solution
            for (int lit = 1; lit < argcount + 1; lit++) {
                sol_buff[lit - 1] = solver->val(lit);
            }
            LOG("prf? ");
            for (int signed_lit : sol_buff) {
                // block every subset of the positive part of the solution by requiring at least one negative literal
                // this is permanently affecting the solver.
                if (signed_lit < 0) ADD_S(-signed_lit);
                // assume positive part of the solution which means it can only be extended in another solve call
                // this is temporarily affecting the solver and is automatically reset at the next solve call.
                else solver->assume(signed_lit);
            }
            ADD_S(0);
            res = solver->solve();
            LOG(res); NL;
        } while (res == 10); // this condition lets the solver extend the solution until there are no more extensions

        // at this point, a single solution found by the while-loop was extended by the do-while-loop to its subset-maximum
        // and all subsets of this solution (including the solution itself) are already blocked

        bool first_out = true;
        for (int signed_lit : sol_buff){
            if (signed_lit > 0) {
                if (first_out) {
                    cout << "\t[" << lit2arg[signed_lit];
                    first_out = false;
                } else {
                    cout << ',' << lit2arg[signed_lit];
                }
            }
        }
        if (first_out) cout << "\t[";
        cout << "]\n" << flush;
    }

    cout << "]\n" << flush;

    delete solver;

    for (const auto &a : pre) {
        delete a.second;
    }

    delete pre_counts;

    return 0;
}
