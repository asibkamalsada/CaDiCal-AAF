#include <algorithm>
//
// Created by asib1 on 22.03.2021.
//

#include "cadical.hpp"
#include <string>
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <cstring>

using namespace std;

#define DEBUG 0

#define LOG(S) if (DEBUG) cout << S

#define ADD(X) LOG(X); solver->add(X)

#define SPACE LOG(' ')
#define NL LOG('\n')

#define ADD_S(X) ADD(X); SPACE
#define TERM_CL ADD(0); NL

int main(__unused int argc, char *argv[]) {
    auto *solver = new CaDiCaL::Solver;
    solver->set("quiet", 1);

    unordered_map<std::string, int> arg2lit;
    unordered_map<int, std::string> lit2arg;

#define B_SIZE 20

    char b[B_SIZE];

    char ch;
    fstream fin(argv[1], fstream::in);

    int argcount = 0;

    bool args_finished = false;

    int *pre_counts;
    int *suc_counts;

    // in fact these are as valid as unordered maps
    // int **pre;
    // int **suc;

    unordered_map<int, int *> pre;
    unordered_map<int, int *> suc;

    while (fin >> noskipws >> ch) {
        if (ch == 'a') {
            fin >> noskipws >> ch;
            if (ch == 'r') {
                fin >> noskipws >> ch;
                if (ch == 'g') {
                    fin >> noskipws >> ch;
                    if (ch == '(') {
                        fin >> noskipws >> ch;
                        unsigned int counter = 0;
                        while (ch != ')') {
                            if (counter > B_SIZE) exit(1);
                            b[counter] = ch;
                            fin >> noskipws >> ch;
                            counter++;
                        }
                        argcount++;
                        std::string s(b, counter);
                        arg2lit[s] = argcount;
                        lit2arg[argcount] = s;
                    }
                }
            } else if (ch == 't') {
                fin >> noskipws >> ch;
                if (ch == 't') {
                    fin >> noskipws >> ch;
                    if (ch == '(') {
                        if (!args_finished) {
                            args_finished = true;
                            solver->reserve(argcount);
                            pre_counts = (int *) calloc(argcount, sizeof(int));
                            suc_counts = (int *) calloc(argcount, sizeof(int));
                            for (int i = 0; i < argcount; i++) {
                                pre[i] = new int[argcount];
                                suc[i] = new int[argcount];
                            }
                            LOG("conflictfree\n");
                        }
                        // conflictfree
                        int lit1;
                        int lit2;
                        fin >> noskipws >> ch;
                        unsigned int counter = 0;
                        while (ch != ',') {
                            if (counter > B_SIZE) exit(1);
                            b[counter] = ch;
                            fin >> noskipws >> ch;
                            counter++;
                        }
                        lit1 = arg2lit[std::string(b, counter)];
                        ADD_S(-lit1);
                        fin >> noskipws >> ch;
                        counter = 0;
                        while (ch != ')') {
                            if (counter > B_SIZE) exit(1);
                            b[counter] = ch;
                            fin >> noskipws >> ch;
                            counter++;
                        }
                        lit2 = arg2lit[std::string(b, counter)];
                        ADD_S(-lit2);
                        TERM_CL;
                        pre[lit2 - 1][pre_counts[lit2 - 1]] = lit1;
                        pre_counts[lit2 - 1]++;

                        suc[lit1 - 1][suc_counts[lit1 - 1]] = lit2;
                        suc_counts[lit1 - 1]++;

                    }
                }
            }
        }
    }


    // might be faster to cache the clauses and add them once to the solver at the end of one loop over argcount

#define ATT pre[i][pre_count]
#define ATT_I ATT - 1

    for (int i = 0; i < argcount; i++) {
#       define loop_lit (i + 1)
        // admissible
        for (int pre_count = 0; pre_count < pre_counts[i]; pre_count++) {
            LOG("adm ");
            for (int pre_pre_count = 0; pre_pre_count < pre_counts[ATT_I]; pre_pre_count++) {
                ADD_S(pre[ATT_I][pre_pre_count]);
            }
            ADD_S(-(loop_lit));
            TERM_CL;
        }
    }
#if DEBUG
    for (const auto &a : arg2lit) {
        cout << a.first << " " << a.second << '\n';
    }
    cout << argcount << '\n';
#endif
    // caches the solution
    int sol_buff[argcount];
    // copy of the amount of attackers every argument has (in order to later reduce this value to check whether there
    // are attackers left or not
    int *pre_count_copy = (int *) malloc(sizeof(int) * argcount);

    cout << "[\n" << flush;

    while (solver->solve() == 10) {
        // actual copying of the amount of attackers every argument has
        memcpy(pre_count_copy, pre_counts, sizeof(int) * argcount);
        // caches whether an argument has already been an attacker (or better: disabler, since these attackers are
        // going to disable other attackers (basically the middle argument in the defender definition)
        bool attacked[argcount];
        for (int i = 0; i < argcount; i++) attacked[i] = false;
        // for each argument i + 1
        for (int i = 0; i < argcount; i++) {
            // if it is in the extension
            if ((sol_buff[i] = solver->val(i + 1)) > 0) {
                // iterate over the successors (middle arguments)
                for (int suc_count = 0; suc_count < suc_counts[i]; suc_count++) {
                    // if they hasn't been middle argument yet
                    if (!attacked[suc[i][suc_count] - 1]) {
                        // every attacked argument by them
                        for (int suc_suc_count = 0;
                            suc_suc_count < suc_counts[suc[i][suc_count] - 1]; suc_suc_count++) {
                            // loses an attacker
                            pre_count_copy[suc[suc[i][suc_count] - 1][suc_suc_count] - 1]--;
                        }
                        // makes sure one middle man cannot be deactivated multiple times
                        attacked[suc[i][suc_count] - 1] = true;
                    }
                }
            }
        }

        bool breach = false;
        // if there is an argument with no attackers left it must be in the solution
        for (int i = 0; i < argcount; i++) if ((breach = (pre_count_copy[i] == 0 && sol_buff[i] < 0))) break;

        if (!breach) {
            bool first_out = true;
            for (int lit = 1; lit < argcount + 1; lit++) {
                if ((sol_buff[lit - 1] = solver->val(lit)) > 0) {
                    if (first_out) {
                        cout << "\t[" << lit2arg[lit];
                        first_out = false;
                    } else {
                        cout << ',' << lit2arg[lit];
                    }
                }
            }
            if (first_out) cout << "\t[";
            cout << "]\n" << flush;
        }

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
    delete pre_count_copy;

    return 0;
}
