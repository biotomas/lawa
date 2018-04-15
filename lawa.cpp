/**
* Lawa - Lazy Walksat Local search
* Author: Tomas Balyo (tomas.balyo@kit.edu)
* Karlsruhe Institure of Technology
*/
#include <stdio.h>
#include <ctype.h>
#include <vector>
#include <cmath>
#include <cstdlib>

using namespace std;

#define ISTRUE(lit) (tvalues[abs(lit)]==lit)

int numVariables;
int numClauses;
int* tvalues;
char* satLits;

struct Clause {
    int numLits;
    int* lits;
};

Clause* clauses;

vector<int>* posOccList;
vector<int>* negOccList;
vector<int> unsatClauseIds;


void printClause(const Clause& cls) {
    for (int li = 0; li < cls.numLits; li++) {
        printf("%d ", cls.lits[li]);
    }
    printf("0 \n");
}

void printModel() {
    for (int var = 1; var <= numVariables; var++) {
        printf("%d ", tvalues[var]);
    }
    printf("\n");
}

void printDebug() {
    for (int ci = 0; ci < numClauses; ci++) {
        printf("%d: ",ci);
        printClause(clauses[ci]);
    }
    printModel();
}


void initializeSearch() {
    tvalues = new int[numVariables+1];
    satLits = new char[numClauses];

    for (int var = 1; var <= numVariables; var++) {
        tvalues[var] = rand()%2 == 0 ? var : -var;
    }

    for (int ci = 0; ci < numClauses; ci++) {
        Clause& cls = clauses[ci];
	char slits = 0;
        for (int li = 0; li < cls.numLits; li++) {
            int lit = clauses[ci].lits[li];
            if (ISTRUE(lit))
                slits++;
        }
        if (slits == 0) {
            unsatClauseIds.push_back(ci);
        }
	satLits[ci]=slits;
    }
}

int computeMakeScore(int lit) {
    int score = 0;
    vector<int>& occList = lit > 0 ? posOccList[lit] : negOccList[-lit];
    for (int cid : occList) {
        if (satLits[cid] == 0) {
            score++;
        }
    }
    return score;
}

int computeBreakScore(int lit) {
    int score = 0;
    vector<int>& occList = lit > 0 ? negOccList[lit] : posOccList[-lit];
    for (int cid : occList) {
        if (satLits[cid] == 1) {
            score++;
        }
    }
    return score;
}

void flipLiteral(int lit) {
    int var = abs(lit);
    vector<int>& decOccList = lit > 0 ? negOccList[var] : posOccList[var];
    vector<int>& incOccList = lit > 0 ? posOccList[var] : negOccList[var];

    for (int cid : decOccList) {
        satLits[cid]--;
        if (satLits[cid] == 0) {
            unsatClauseIds.push_back(cid);
        }
    }
    for (int cid : incOccList) {
        satLits[cid]++;
    }

    tvalues[var] = lit;
}

void search() {
    unsigned long round = 0;
    while (unsatClauseIds.size() > 0) {
        round++;
        //printf("c round %lu, unsat clauses: %lu\n", round, unsatClauseIds.size());
        int usidid = rand() % unsatClauseIds.size();
        int usid = unsatClauseIds[usidid];
        unsatClauseIds[usidid] = unsatClauseIds.back();
        unsatClauseIds.pop_back();
        Clause& cls = clauses[usid];
        if (satLits[usid] > 0) {
            continue;
        }
        //printf("c will satisfy clause ");
        //printClause(cls);

        int id1 = rand() % cls.numLits;
        int id2 = rand() % cls.numLits;
        while(id1 == id2) {
            id1 = rand() % cls.numLits;
            id2 = rand() % cls.numLits;
        }
        int lit1 = cls.lits[id1]; 
        int lit2 = cls.lits[id2];

        int score1 = computeMakeScore(lit1) - computeBreakScore(lit1);// - flippedCount[abs(lit1)];
        int score2 = computeMakeScore(lit2) - computeBreakScore(lit2);// - flippedCount[abs(lit2)];

        if (score1 == score2) {
            //printf("c flipping %d and %d, their score: %d\n", lit1, lit2, score1);
            flipLiteral(lit1);
            flipLiteral(lit2);
        } else {
            int toFlip = score1 > score2 ? lit1 : lit2;
            //printf("c flipping %d, its score is max (%d, %d)\n", toFlip, score1, score2);
            flipLiteral(toFlip);
        }
    }
    printf("c searched finished after %lu rounds.\n", round);
}


void makeOccurrenceLists() {
    posOccList = new vector<int>[1+numVariables];
    negOccList = new vector<int>[1+numVariables];
    for (int ci = 0; ci < numClauses; ci++) {
        for (int li = 0; li < clauses[ci].numLits; li++) {
            int lit = clauses[ci].lits[li];
            int var = abs(lit);
            if (lit > 0) {
                posOccList[var].push_back(ci);
            } else {
                negOccList[var].push_back(ci);
            }
        }
    }
}

int readNextNumber(FILE* f, int c) {
    while (!isdigit(c)) {
        c = fgetc(f);
    }
    int num = 0;
    while (isdigit(c)) {
        num = num*10 + (c-'0');
        c = fgetc(f);
    }
    return num;
}

void readLine(FILE* f) {
    int c = fgetc(f);
    while(c != '\n') {
        c = fgetc(f);
    }
}

bool loadSatProblem(const char* filename) {
    FILE* f = fopen(filename, "r");
    if (f == NULL) {
        return false;
    }
    int c = 0;
    bool neg = false;
    int clauseInd = 0;
    vector<int> tmpClause;
    while (c != EOF) {
        c = fgetc(f);

        // comment line
        if (c == 'c') {
            readLine(f);
            continue;
        }
        // problem lines
        if (c == 'p') {
            numVariables = readNextNumber(f, 0);
            numClauses = readNextNumber(f, c);
            clauses = new Clause[numClauses];
            continue;
        }
        // whitespace
        if (isspace(c)) {
            continue;
        }
        // negative
        if (c == '-') {
            neg = true;
            continue;
        }

        // number
        if (isdigit(c)) {
            int num = readNextNumber(f, c);
            if (neg) {
                num *= -1;
            }
            neg = false;
            if (num == 0) {
                clauses[clauseInd].numLits = tmpClause.size();
                clauses[clauseInd].lits = new int[tmpClause.size()];
                for (size_t i = 0; i < tmpClause.size(); i++)
                    clauses[clauseInd].lits[i] = tmpClause[i];
                tmpClause.clear();
                clauseInd++;
            } else {
                tmpClause.push_back(num);
            }
        }
    }
    fclose(f);
    return true;
}

int main(int argc, char** argv) {
    printf("c This is lawa - lazy walksat local search satisfiability solver\n");
    printf("c USAGE: ./lawa <cnf-formula-in-dimacs-format>\n");
    if (!loadSatProblem(argv[1])) {
        printf("ERROR: problem not loaded\n");
        return 1;
    }
    srand(2018);
    makeOccurrenceLists();
    initializeSearch();
    search();
    printf("s SATISFIABLE\nv ");
    printModel();
}
