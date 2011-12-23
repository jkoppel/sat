/*
 * Implementation of the David-Putnam-Logemann-Loveland algorithm.
 * Uses the most-constrained variable-ordering heuristic
 * and the most-common sign value-ordering heuristic
 *
 * Created for Homework 2 of 15-780, Graduate Artificial Intelligence, Spring 2011.
 * Conflict-directed backjumping added for Homework 3
 *
 * Accepts DIMACS CNF format sans comments through stdin.
 * Comments should be stripped out (e.g.: with sed) before running.
 *
 * Author: James Koppel
 * E-mail: jkoppel@andrew.cmu.edu
 */

#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include<time.h>
#include<set>
#include<new>

using namespace std;

/* Reading the input becomes a *lot* harder without assuming
 * clauses can have a maximum size
 *
 * Yes, this is a buffer-overflow vulnerability.
 */
#define MAX_CLAUSE_SIZE 1000

int V; //Number of variables
int C; //Number of clauses

/*
 * For each variable, an array of all clauses it appears in
 * The encoding is similar to the encoding of the appearance of variables
 * in clauses -- one plus the 0-indexed ID of the clause, and signed
 * to determine whether the variable occurs positively therein
 */
int **appearances; 
int (*clauses)[MAX_CLAUSE_SIZE]; //For each clause, list of its literals
int *csizes;
int *napps;
int *npos_app;
int *nneg_app;

int *assn; //1 for true, -1 for false, 0 for unset

/*
 * For each clause, either 0, or the ID of the variable which satisfied it
 * in the DFS
 */
int *satisfier;

/*
 * For each clause, number of unset variables contained therein.
 */
int *rem;
int nunsat;

/*
 *Next three values are used for unit propagation.
 */
int *propagation_queue;
int npropped; //size of propagation queue
int *npropped_at; //cache of npropped at each stage of dfs
int *propping_clause;

set<int> *conflict;
set<int> *in_conflict;


bool assign(int v, int sign);
void unassign_upto(int v, int sign, int upto);
bool dfs(int l);


void print_in_conflict_set(int v) {
  char *sep = "";
  printf("conflict set for %d:", v);
  for(set<int>::iterator it = in_conflict[v].begin(); it != in_conflict[v].end(); it++) {
    printf("%s%d",sep, *it);
    sep = " ";
  }
  printf("\n");
}

void print_conflict_set(int v) {
  char *sep = "";
  printf("conflict set for %d:", v);
  for(set<int>::iterator it = conflict[v].begin(); it != conflict[v].end(); it++) {
    printf("%s%d",sep, *it);
    sep = " ";
  }
  printf("\n");
}

bool in_conflict_set(int v) {
  return !in_conflict[v].empty();
}

void augment_conflict(int v) {
  for(set<int>::iterator o = in_conflict[v].begin(); o != in_conflict[v].end(); o++) {
    for(set<int>::iterator it = conflict[*o].begin(); it != conflict[*o].end(); it++) {
      if(*it != v) {
	conflict[v].insert(*it);
	in_conflict[*it].insert(v);
      }
    }
  }
  in_conflict[v].clear();
}

void backprop_conflict(int v, int c) {
  for(int j = 0; j < csizes[c]; j++) {
    int varid = abs(clauses[c][j])-1;
    if(varid != v) {
      conflict[v].insert(abs(clauses[c][j])-1);
      in_conflict[varid].insert(v);
    }
  }
  augment_conflict(v);
}

void enqueue_unit_propagation(int c) {
  for(int i = 0; i < csizes[c]; i++) {
    int v = clauses[c][i];
    int varid = abs(v)-1;
    if(assn[varid] == 0) {
      propagation_queue[npropped++] = v;
      propping_clause[varid] = c;
      return;
    }
  }
}

void modify_signed_appearances(int c, int inc) {
  for(int i = 0; i < csizes[c]; i++) {
    int v = clauses[c][i];
    int varid = abs(v)-1;
    if(v<0)
      nneg_app[v] += inc;
    else
      npos_app[v] += inc;
  }
}

void mark_signed_appearances(int c) {
  modify_signed_appearances(c, 1);
}

void unmark_signed_appearances(int c) {
  modify_signed_appearances(c, -1);
}

bool assign(int v, int sign) {
  if(assn[v])
    return true;
  
  assn[v] = sign;

  int nprop = 0;
  
  for(int i = 0; i < napps[v]; i++) {
    
    int c = abs(appearances[v][i])-1;
    rem[c]--;
    
    if(appearances[v][i] * sign > 0) {
      if(satisfier[c] == 0) {
	satisfier[c] = v+1;
	nunsat--;
	mark_signed_appearances(c);
      }
    } else {
      if(sign < 0)
	nneg_app[v]--;
      else
	npos_app[v]++;
      
      if(satisfier[c]==0) {

	if(rem[c]==0) {
	  //printf("contradiction on %d in clause %d\n",v,c);
	  backprop_conflict(v, c);
	  unassign_upto(v,sign,i+1);
	  return false;
	}

	if(rem[c]==1) {
	  enqueue_unit_propagation(c);
	}
      }
    }
  }

  return true;
}

void unassign_upto(int v, int sign, int upto) {

  if(!assn[v])
    return;
  
  assn[v] = 0;
  
  for(int i = 0; i < upto; i++) {
    int c = abs(appearances[v][i])-1;
    rem[c]++;
    if(appearances[v][i] * sign > 0) {
      if(satisfier[c] == v+1) {
	satisfier[c] = 0;
	nunsat++;
	unmark_signed_appearances(c);
      }
    } else {

      if(sign<0)
	nneg_app[v]++;
      else
	npos_app[v]++;
    }
  }
}

void unassign(int v, int sign) {
  unassign_upto(v, sign, napps[v]);
}

void undo_unit_propagations(int low, int high) {
  for(int i = high-1; i >= low; i--) {
    int app = propagation_queue[i];
    int varid = abs(app)-1;
    backprop_conflict(varid, propping_clause[varid]);
    int sign = app > 0 ? 1 : -1;
    unassign(varid, sign);
  }

  npropped = low;
}

bool do_unit_propagations(int from) {
  for(int i = from; i < npropped; i++) {
    int app = propagation_queue[i];
    int varid = abs(app)-1;
    in_conflict[varid].clear();
    conflict[varid].clear();
    int sign = app > 0 ? 1 : -1;
    if(!assign(varid, sign)) {
      undo_unit_propagations(from, i);
      return false;
    } 
  }
  return true;
}

bool try_value(int v, int sign, int l) {
  //printf("%d: trying %d=%d\n",l,v,sign);

  if(assign(v, sign)) {
    if(do_unit_propagations(npropped_at[v])) {
      if(dfs(l+1))
	return true;
      undo_unit_propagations(npropped_at[v], npropped);
    }
    unassign(v,sign);
  }
  return false;
}

int most_constrained_var() {
  int mapp = 0;
  int v = -1;
  
  for(int i = 0; i < V; i++) {
    if(assn[i])
      continue;
    
    if(npos_app[i]+nneg_app[i]>mapp) {
      v = i;
      mapp = npos_app[i]+nneg_app[i];
    }
  }

  return v;
}

int random_next_var() {
  int nleft = 0;
  for(int i = 0; i < V; i++) {
    if(!assn[i])
      nleft++;
  }

  if(nleft==0)
    return -1;
  
  int nxt = rand()%nleft;

  int on = 0;
  for(int i = 0; i < V; i++) {
    if(assn[i])
      continue;

    if(on==nxt)
      return i;

    on++;
  }
  return -1;
  
}

bool dfs(int l) {
  
  if(nunsat == 0)
    return true;

  int v = most_constrained_var();
  //int v = random_next_var();
  
  if(v == -1)
    return false;

  int first_try, second_try;

  if(npos_app[v] > nneg_app[v]) {
    first_try = 1;
    second_try = -1;
  } else {
    first_try = -1;
    second_try = 1;
  }
  
  npropped_at[v] = npropped;
  
  conflict[v].clear();
  in_conflict[v].clear();
  
  if(try_value(v, first_try, l))
    return true;

  if(in_conflict_set(v)) {
    // if(true) {
    augment_conflict(v);
    return try_value(v, second_try, l);
  } else {
    //printf("backjumping past %d\n", l);
    //print_conflict_set(v);
    return false;
  }
}

int main() {

  srand(time(NULL));
  
  //Skipping past blank lines stripped of comments
  char ch = '\0';
  while(ch != 'p') scanf("%c", &ch);
	
  if(scanf(" cnf %d %d", &V, &C) < 2) {
    fprintf(stderr, "Failed to read input\n");
    return 1;
  }



  /* Initialization of data structure */
  clauses = (int (*)[MAX_CLAUSE_SIZE])malloc(C*MAX_CLAUSE_SIZE*sizeof(int));

  npos_app = (int*)calloc(V, sizeof(int));
  nneg_app = (int*)calloc(V, sizeof(int));
  napps = (int*)calloc(V, sizeof(int));
  csizes = (int*)calloc(C, sizeof(int));

  //Large, as I don't prevent variables from being queued
  //multipled times
  propagation_queue = (int*)calloc(V*C, sizeof(int));
  
  npropped = 0;
  npropped_at = (int*)calloc(V, sizeof(int));
  propping_clause = (int*)malloc(V * sizeof(int));

  conflict = new set<int> [V];
  in_conflict = new set<int> [V];

  /*
   * A two-pass approach to reading the input.
   * First, we read in the clauses. Then, we
   * count the number of occurences of each variable
   * and initialize the list of occurences of said
   * variable
   */
  for(int i = 0; i < C; i++) {
    int s = 0;
    
    while(true) {
      int v;
      scanf("%d",&v);

      if(v==0)
	break;
      
      clauses[i][s++] = v;

      int varid = abs(v)-1;
      napps[varid]++;
      
      if(v<0)
	nneg_app[varid]++;
      else
	npos_app[varid]++;
    }
    
    csizes[i] = s;
  }

  appearances = (int**)malloc(V*sizeof(int*));

  /*
   * napps is used both for initially counting
   * each variable, and for tracking
   * how much the array of appearances
   * has been filled
   */
  for(int i = 0; i < V; i++) {
    appearances[i] = (int*)malloc(napps[i]*sizeof(int));
    napps[i] = 0;
  }
  
  for(int i = 0; i < C; i++) {
    for(int j = 0; j < csizes[i]; j++) {
      int varid = abs(clauses[i][j])-1;
      int app_enc;
      
      if(clauses[i][j] < 0)
	app_enc = -(i+1);
      else
	app_enc = i+1;
	 
      appearances[varid][napps[varid]++] = app_enc;
    }
  }

  assn = (int*)calloc(V, sizeof(int));
  satisfier = (int*)calloc(C, sizeof(int));
  rem = (int*)malloc(C*sizeof(int));

  for(int i = 0; i < C; i++)
    rem[i] = csizes[i];

  nunsat = C;

  if(dfs(0)) {
    for(int i = 0; i < V; i++)
      printf("%d %d\n", i+1, assn[i] > 0 ? 1 : 0);
  } else {
    printf("UNSAT\n");
  }



  delete [] in_conflict;
  delete [] conflict;
  
  free(propagation_queue);
  free(propping_clause);
  free(npropped_at);
  
  free(rem);
  free(satisfier);
  free(assn);
  
  /* Cleanup */
  for(int i = 0; i < V; i++)
    free(appearances[i]);

  free(appearances);
  
  free(clauses);
  free(csizes);
  free(napps);
  free(npos_app);
  free(nneg_app);

  return 0;
}
