#ifndef DB_H
#define DB_H

#define FILENAME "db.dat"
#define STRLEN 50

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#include "LatticeUsed.h"
static labelType ctx = 0;

void setCurrent ( labelType l ) { ctx = l;}
labelType getCurrent( void *unit) {return ctx; }

void fail(const char *s) {
  printf("%s\n", s);
  exit(1);
}
//typedef char* Prims_string;

/* #include "DBStar.h" */

/* #define assert(d, a) {if (!(a)) {printf("assertion failed: %s\n", d); exit(EXIT_FAILURE);}} */

/* #define getTag(a) a.label */
/* #define getData(a) a.value */

#endif
