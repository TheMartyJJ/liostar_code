#ifndef DB_H
#define DB_H

#define FILENAME "db.dat"
#define STRLEN 50

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#include "LatticeUsed.h"
static labels ctx = 0;

void setCurrent ( labels l ) { ctx = l;}
labels getCurrent( void *unit) {return ctx; }

void fail(const char *s) {
  printf("%s\n", s);
  exit(1);
}
//typedef char* Prims_string;

#include "DBStar.h"

#define assert(d, a) {if (!(a)) {printf("assertion failed: %s\n", d); exit(EXIT_FAILURE);}}

#define getTag(a) a.label
#define getData(a) a.value

typedef box__DBStar_paper  /*struct {
	int 	label;
	int 	id;
	fixedString 	pdf;
	int 	review_label;
	char 	review_data[STRLEN];
}*/ labeled_paper_t;

static labeled_paper_t * database = NULL;
static uint32_t database_size = 0;

void mkDB(uint32_t max){
  database_size = max;

	if (database != NULL)
	  free(database);

	database = malloc(database_size * sizeof(labeled_paper_t));
	
}

uint32_t getDBsize(void*unit){
	// https://www.geeksforgeeks.org/fseek-in-c-with-example/
	FILE *fp; 
    fp = fopen(FILENAME, "r"); 
      
    // Moving pointer to end 
    fseek(fp, 0, SEEK_END); 
    uint32_t r = ftell(fp);
    
    fclose(fp);
      
    // Printing position of pointer 
    return r / sizeof(labeled_paper_t);
}


void loadDB(void*unit){
	uint32_t i = 0;
	FILE *fp; 

	mkDB(getDBsize(NULL));
	
	fp = fopen(FILENAME, "r"); 
	while (i < database_size){
	  fread(&(database[i]),sizeof(labeled_paper_t), 1, fp);
	  i++;
	}
	fclose(fp);
}

void syncDB(void*unit){
  uint32_t i = 0;
	FILE *fp; 
	
	fp = fopen(FILENAME, "w");
	printf("syncing to %s\n", FILENAME);
	while (i < database_size){
	  fwrite(&(database[i]),sizeof(labeled_paper_t), 1, fp);
	  i++;
	}
	fclose(fp);
}

uint32_t getMaxId(void*unit){
  //printf("get max id %d\n", database_size);
  return database_size;
}

uint32_t getFreeId(void*unit){
  uint32_t i = 0;
  while (i < database_size && getData(database[i]).id != 0){
    i++;
  }
  //printf("get free id %d\n", i+1);
  return (i+1); // if i > database_size ==> invalid
}

void setById(uint32_t i, labeled_paper_t p){
  //printf("set paper to id %d\n", i);
  database[i-1] = p;
}


labeled_paper_t getById(uint32_t i) {
  return database[i-1];
}


void print(uint32_t i){
  printf("id found %d\n", i);
}

void printPaper(labeled_paper_t lp){
  uint32_t id = getData(lp).id;
  uint64_t pdf = getData(lp).pdf;
  uint32_t tag = getTag(lp);
  uint32_t optiontag = (getData(lp).review1).tag;
  uint64_t optionv = getData(getData(lp).review1.v);
  uint32_t optionl = getTag((getData(lp).review1.v));
  printf("{\n");
  printf("\tid\t= %d\n", id);
  printf("\ttag\t= %d\n", tag);
  printf("\tpdf\t= %lu\n", pdf);
  printf("\tr1\t= %s %lu\n", (optiontag == 0 ? "None" : "Some"), optionv);
  printf("\tr1 tag\t= %d\n", optionl);
  printf("}\n");
}
/*
void printPaper2(paper lp){
  uint32_t id = p.id;
  uint64_t pdf = p.pdf;
  //uint32_t tag = lp.tag;
  uint32_t optiontag = p.review1.tag;
  uint64_t optionv = getData(p.review1.v);
  printf("{ - paper -\n");
  printf("\tid\t= %d\n", id);
  //printf("\ttag\t= %d\n", tag);
  printf("\tpdf\t= %lu\n", pdf);
  printf("\tr1\t= %s %lu\n", (optiontag == 0 ? "None" : "Some"), optionv);
  printf("}\n");
}*/
/*
void add(char *test){
  int i = (getFreeId() - 1);
  if ((i+1) > database_size)
    printf("nope %d-%d -> %d\n", i, i+1, database_size);
  database[i].id = (i+1);
  strcpy(database[i].pdf, test);
}

int main(void){
	mkDB(10);
	syncDB();
	printf("database is %d size\n", getDBsize());
	printf("free id here %d\n", getFreeId());
	add("hey");add("hey");add("hey");
	add("hey");add("hey");add("hey");
	add("hey");add("hey");add("hey");add("hey");//add("hey");
	printf("free id here %d\n", getFreeId());
	syncDB();
	return 0;
	}*/


#include <sys/resource.h>
#include <stdio.h>

void mkBigStack (void *unit){
const rlim_t kStackSize = 64L * 1024L * 1024L * 20L * 100L;   // min stack size = 64 Mb
    struct rlimit rl;
    int result;

    result = getrlimit(RLIMIT_STACK, &rl);
    if (result == 0)
    {
        if (rl.rlim_cur < kStackSize)
        {
            rl.rlim_cur = kStackSize;
            result = setrlimit(RLIMIT_STACK, &rl);
            if (result != 0)
            {
                fprintf(stderr, "setrlimit returned result = %d\n", result);
            }
        }
    }
}

#include <sys/time.h>
#include <sys/resource.h>

double get_time()
{
    struct timeval t;
    struct timezone tzp;
    gettimeofday(&t, &tzp);
    return t.tv_sec + t.tv_usec*1e-6;
}

static uint32_t benchmax = 0;
static double start;
void startBenchmark(uint32_t max){
  benchmax = max;
  start = get_time();
}

void stopBenchmark(void*unit){
  double stop = get_time();
  double elapsed = stop - start;
  printf("Time %f\n", elapsed);
}

#endif

