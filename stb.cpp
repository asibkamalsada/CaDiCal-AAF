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
                        }

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
                        solver->add(-lit1);
                        solver->add(-lit2);
                        // terminating the clause
                        solver->add(0);

                        // adding lit1 as an attacker of lit2
                        pre[lit2 - 1][pre_counts[lit2 - 1]] = lit1;
                        pre_counts[lit2 - 1]++;

                    }
                }
            }
        }
    }

    // adding an argument and each of its attackers to one final clause as positive literals
    // ensures stable
    for (int i = 0; i < argcount; i++) {
        for (int pre_count = 0; pre_count < pre_counts[i]; pre_count++) {
            solver->add(pre[i][pre_count]);
        }
        solver->add(i + 1);
        solver->add(0);
    }

    // buffers exactly one solution by saving the signed literals of the model of the solver
    int sol_buff[argcount];

    cout << "[\n" << flush;

    // while there are solutions
    while (solver->solve() == 10) {
        // boolean for checking whether it is the first printed argument of the current solution or not
        bool first_out = true;
        // loop over all arguments (in this case unsigned literals representing arguments)
        for (int lit = 1; lit < argcount + 1; lit++) {
            // add the signed literal to the buffer. if it is positive, print it
            if ((sol_buff[lit - 1] = solver->val(lit)) > 0) {
                if (first_out) {
                    cout << "\t[" << lit2arg[lit];
                    first_out = false;
                } else {
                    cout << ',' << lit2arg[lit];
                }
            }
        }
        // if there were no arguments to be printed, print an empty set
        if (first_out) cout << "\t[";
        cout << "]\n" << flush;

        // block the current solution by negating all its signed literals and adding it as a clause to the solver
        for (int signed_lit : sol_buff) {
            solver->add(-signed_lit);
        }
        solver->add(0);
    }

    cout << "]\n" << flush;

    delete solver;

    for (const auto &a : pre) {
        delete a.second;
    }

    delete pre_counts;

    return 0;
}
