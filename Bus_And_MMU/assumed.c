#ifndef ASSUME
#define ASSUME

#define DEBUG_MODE 0// 0 = printf off, 1 = printf on

#include "Bus_Lattice.h"

#define NB_CALL 3
#define MAX 12
static int status = 0;
#define incr(s) (state++)
static int state = 0;

#define Bot 0
#define C 1
#define CM 2
#define M 3
#define E 4

const uint8_t bus_data[MAX] = {65,66,67,68,69,70,71,72,73,74,75,76};
const labels bus_from[MAX] =  {C ,C ,C ,C ,M ,M ,M ,M ,M ,E ,C ,C};
const labels bus_to[MAX] =    {C ,M ,E ,M ,C ,M ,E ,C ,M ,E ,E ,C};

void write(labels a, uint8_t d){
	if (DEBUG_MODE)
		printf("send char '%d' to '%d'\n", d, a);
}

uint8_t read(labels a){
	uint8_t d = bus_data[(state) % MAX];
	labels t = bus_to[state% MAX];
	if (DEBUG_MODE)
		printf("receive char '%d' from '%d' to '%d'\n", d, a, t);
	state++;
	return d;
}

labels getSource(void){
	labels a = bus_from[(state) % MAX];
	return a;
}

labels getDestination(void){
	labels a = bus_to[(state) % MAX];
	return a;
}

static labels ctx = 0;

void setCurrent ( labels l ) { ctx = l;}
labels getCurrent( void ) {return ctx; }

void fail(char *s) {
  printf("%s\n", s);
  exit(1);
}

#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>

//////////////////// MMUStar
#define taskSize 512
#define pageSize 32
#define nbTask 2

static uint8_t * heap = NULL;

void write_memory(uint32_t addr, uint8_t v){
        heap[addr] = v;
}

uint8_t read_memory(uint32_t addr){
        return heap[addr];
}



void mkBigStack (void ){
const rlim_t kStackSize = 64L * 1024L * 1024L * 20L * 10L;   // min stack size = 64 Mb
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
heap = malloc(taskSize * pageSize * nbTask);	
}


#endif
