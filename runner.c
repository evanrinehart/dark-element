#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

// C program which continually applies the evaluation rule

enum H
  {UNIT,T,F,Z,NIL,S,P,CONS,INT,DO,LAM,
  IF,ITER,AT,PR1,PR2,FOLD,
  IND,FWD,BIND,PACK,SEQ};
// other things... ADDR, DOUBLE, BUFFER, CELL, VECTOR

enum GI {COPYX, COPYC, PRINT1, PRINT2, PRINT3};
enum subop {RPLUS, IMM, X, CLO, ADDR};

enum reason
  {FFI_EOF, FFI_ARGUMENT_ERROR, FFI_EXIT};

struct obj;

union component{
  int i;
  struct obj* ptr;
  //void* addr;   (foreign pointer)
  //double d;     (raw double)
  //unsigned char* buf; (byte array)
  //cell*              (mutable cell)
  //struct obj** vec;  (vector of boxed)
};
// other things... ADDR, DOUBLE, BUFFER, CELL, VECTOR

typedef union component ucom;

struct obj {
  enum H h;
  union component com[3];
};

struct genIn {
  enum GI type;
  enum H K;
  enum subop sub[3];
  int pay[3];
};

struct runtime {
  int heapSize;
  int heapPtr;
  struct obj* heap;
  struct obj* oldHeap;
  int stackSize;
  int stackPtr;
  struct obj** stack;
  int exceptionStackPtr;
  struct obj* exceptionStack[64];
  struct obj unit;
  struct obj ff;
  struct obj tt;
  struct obj nil;
  struct obj zero;
  enum reason stuckReason;
  struct obj* cursor;
  struct obj* root;
};

struct ffi {
  char name[64];
  int spaceNeeded;
  struct obj* (*execute)(struct obj* x, struct obj* k, struct runtime* rts);
};

struct sizedGen {
  int size;
  struct genIn* code;
};

struct sizedGen generators[4096];

struct ffi ffiBindings[64];

int isVal(struct obj* o, int dontExec){
  if(dontExec > 0 && o->h == BIND) return 1;
  if(o->h <= LAM) return 1;
  else            return 0;
}

// Stack and Heap operations

void growStack(struct runtime* rts){
  rts->stackSize *= 2;
  struct obj** tmp;
  tmp = realloc(rts->stack, rts->stackSize * sizeof(struct obj*));
  if(tmp == NULL){
    fprintf(stderr, "failed to grow stack (%s)\n", strerror(errno));
    exit(-1);
  }
  rts->stack = tmp;
}

void push(struct obj* ptr, struct runtime* rts){
  if(rts->stackPtr+1 == rts->stackSize) growStack(rts);
  rts->stack[rts->stackPtr] = ptr;
  rts->stackPtr++;
}

struct obj* pop(struct runtime* rts){
  if(rts->stackPtr == 0){
    fprintf(stderr, "stack underflow\n");
    exit(-1);
  }
  rts->stackPtr--;
  return rts->stack[rts->stackPtr];
}

struct obj* putObj(enum H h, struct runtime* rts){
  struct obj* ptr = rts->heap + rts->heapPtr;
  rts->heap[rts->heapPtr].h = h;
  rts->heapPtr++;
  return ptr;
}

struct obj* put1(enum H h, ucom x, struct runtime* rts){
  struct obj* o = putObj(h,rts);
  o->com[0] = x;
  return o;
}

ucom put1u(enum H h, ucom x, struct runtime* rts){
  ucom v = {.ptr = put1(h,x,rts) };
  return v;
}

struct obj* put1i(enum H h, int i, struct runtime* rts){
  struct obj* o = putObj(h, rts);
  o->com[0].i = i;
  return o;
}

struct obj* put2(enum H h, ucom x, ucom y, struct runtime* rts){
  struct obj* o = putObj(h,rts);
  o->com[0] = x;
  o->com[1] = y;
  return o;
}

struct obj* put2p(enum H h, struct obj* x, struct obj* y, struct runtime* rts){
  struct obj* o = putObj(h, rts);
  o->com[0].ptr = x;
  o->com[1].ptr = y;
  return o;
}

struct obj* put3(enum H h, ucom x, ucom y, ucom z, struct runtime* rts){
  struct obj* o = putObj(h, rts);
  o->com[0] = x;
  o->com[1] = y;
  o->com[2] = z;
  return o;
}

struct obj* put3p(enum H h, struct obj* x, struct obj* y, struct obj* z, struct runtime* rts){
  struct obj* o = putObj(h, rts);
  o->com[0].ptr = x;
  o->com[1].ptr = y;
  o->com[2].ptr = z;
  return o;
}

ucom put3u(enum H h, ucom x, ucom y, ucom z, struct runtime* rts){
  ucom v = {.ptr = put3(h,x,y,z,rts) };
  return v;
}

struct obj* cloneObj(struct obj* orig, struct runtime* rts){
  struct obj* ptr = rts->heap + rts->heapPtr;
  rts->heap[rts->heapPtr] = *orig;
  rts->heapPtr++;
  return ptr;
}

struct obj* cloneClosure(struct obj* orig, int size, struct runtime* rts){
  int i;
  struct obj* clo;
  for(i=0; i<size; i++){
    clo = cloneObj(&orig[i], rts);
  }
  // awkwardly clo points to the last element, go back size-1
  return clo - (size - 1);
}


// Exception stuff

struct obj* popExStack(struct runtime* rts){
  if(rts->exceptionStackPtr == 0){
    fprintf(stderr, "exception stack underflow\n");
    exit(-1);
  }

  rts->exceptionStackPtr--;
  return rts->exceptionStack[rts->exceptionStackPtr];
}

void pushExStack(struct obj* x, struct runtime* rts){
  // FIXME
}

struct obj* mkFrame(struct obj* act, struct obj* k, struct runtime* rts){
  // let mkFrame = \act k -> act >>= (\x -> pop >>= \_ -> k x)
  // be a pregenerated "frame maker" function
  // then this procedure generates: (mkFrame @ act) @ k
  // and so requires 2 space.
  return NULL; // act >>= (\x -> pop >>= \_ -> k x)
}

struct obj* mkHandler(struct obj* h, struct obj* k, struct runtime* rts){
  // let mkHandler = \h k -> \ex -> h ex >>= k
  // be a pregnerated "handler maker" function
  // then this procedure generates: (mkHandler @ h) @ k
  // and so requires 2 space
  return NULL; // \ex -> h ex >>= k
}



// Printers So We Can Tell What's Going On

#define REL(o,i) (o->com[i].ptr - rts->heap)

void printObj(struct obj* o, struct runtime* rts){
  switch(o->h){
    case UNIT: printf("○\b●\n"); return;
    case T:    printf("T\n"); return;
    case F:    printf("F\n"); return;
    case Z:    printf("Z\n"); return;
    case S:    printf("S %ld\n",REL(o,0)); return;
    case P:    printf("P %ld %ld\n",REL(o,0),REL(o,1)); return;
    case NIL:  printf("NIL\n"); return;
    case CONS: printf(":: %ld %ld\n",REL(o,0),REL(o,1)); return;
    case LAM:  printf("λ %d g%d\n", o->com[0].i, o->com[1].i); return;
    case IF:   printf("IF %ld %ld %ld\n",REL(o,0),REL(o,1),REL(o,2)); return;
    case ITER: printf("ITER %ld %ld %ld\n",REL(o,0),REL(o,1),REL(o,2)); return;
    case FOLD: printf("FOLD %ld %ld %ld\n",REL(o,0),REL(o,1),REL(o,2)); return;
    case PR1:  printf("PR1 %ld\n",REL(o,0)); return;
    case PR2:  printf("PR2 %ld\n",REL(o,0)); return;
    case AT:   printf("@ %ld %ld\n",REL(o,0),REL(o,1)); return;
    case FWD:  printf("FWD %ld\n",REL(o,0)); return;
    case IND:  printf("IND %ld\n",REL(o,0)); return;
    case INT:  printf("INT %d\n", o->com[0].i); return;
    case DO:  printf("DO %s %ld\n", ffiBindings[o->com[0].i].name, REL(o,1)); return;
    case BIND:  printf("BIND %ld %ld\n", REL(o,0), REL(o,1)); return;
    case PACK:  printf("PACK %ld\n",REL(o,0) ); return;
    case SEQ:  printf("SEQ %ld %ld\n", REL(o,0), REL(o,1)); return;
  }
}

void printK(enum H k){
  switch(k){
    case UNIT: printf("UNIT "); return;
    case T:    printf("T "); return;
    case F:    printf("F "); return;
    case Z:    printf("Z "); return;
    case S:    printf("S "); return;
    case P:    printf("P "); return;
    case NIL:  printf("NIL "); return;
    case CONS: printf("CONS "); return;
    case LAM:  printf("λ "); return;
    case IF:   printf("IF "); return;
    case ITER: printf("ITER "); return;
    case FOLD: printf("FOLD "); return;
    case PR1:  printf("PR1 "); return;
    case PR2:  printf("PR2 "); return;
    case AT:   printf("@ "); return;
    case IND:  printf("IND "); return;
    case FWD:  printf("FWD "); return;
    case INT: printf("INT "); return;
    case DO: printf("DO "); return;
    case BIND: printf("BIND "); return;
    case PACK: printf("PACK "); return;
    case SEQ: printf("SEQ "); return;
  }
}

void printHeap(struct runtime* rts){
  int i;
  char num[16];
  int a = 0;
  int b = rts->heapPtr;
  int digits = 0;
  int tmp = b;
  while(tmp > 0){ digits++; tmp /= 10; }
  digits = digits < 1 ? 1 : digits;
  digits += 2;

  for(i=a; i<b; i++){
    if(rts->heap+i==rts->root) printf("> ");
    else printf("  ");
    sprintf(num,"%d.",i);
    printf("%-*s ",digits,num);
    printObj(rts->heap+i, rts);
  }
}

void printSubop(enum subop so){
  switch(so){
    case RPLUS:  printf("r+ ");  break;
    case IMM:    printf("imm "); break;
    case X:      printf("x ");   break;
    case CLO:    printf("c[] "); break;
    case ADDR:   printf("addr "); break;
    default:
      fprintf(stderr, "print subop failed\n");
      exit(-1);
  }
}

void printGenIn(struct genIn gi){
  switch(gi.type){
    case COPYX:
      printf("copyx\n");
      break;
    case COPYC:
      printf("copyc %d\n", gi.pay[0]);
      break;
    case PRINT1:
      printf("print1 ");
      printK(gi.K);
      printSubop(gi.sub[0]);
      printf("%d\n", gi.pay[0]);
      break;
    case PRINT2:
      printf("print2 ");
      printK(gi.K);
      printSubop(gi.sub[0]);
      printSubop(gi.sub[1]);
      printf("%d %d\n", gi.pay[0], gi.pay[1]);
      break;
    case PRINT3:
      printf("print3 ");
      printK(gi.K);
      printSubop(gi.sub[0]);
      printSubop(gi.sub[1]);
      printSubop(gi.sub[2]);
      printf("%d %d %d\n", gi.pay[0], gi.pay[1], gi.pay[2]);
      break;
    default:
      fprintf(stderr, "print genIn failed\n");
      exit(-1);
  }
}

void printGen(struct sizedGen sg){
  printf("%d\n", sg.size);
  int i;
  for(i=0; i<sg.size; i++){
    printGenIn(sg.code[i]);
  }
}


// Generator Loader

enum H strToH(char* s){
  if(strcmp(s, "UNIT")==0) return UNIT;
  else if(strcmp(s, "T")==0) return T;
  else if(strcmp(s, "F")==0) return F;
  else if(strcmp(s, "Z")==0) return Z;
  else if(strcmp(s, "S")==0) return S;
  else if(strcmp(s, "P")==0) return P;
  else if(strcmp(s, "NIL")==0) return NIL;
  else if(strcmp(s, "CONS")==0) return CONS;
  else if(strcmp(s, "LAM")==0) return LAM;
  else if(strcmp(s, "IF")==0) return IF;
  else if(strcmp(s, "ITER")==0) return ITER;
  else if(strcmp(s, "AT")==0) return AT;
  else if(strcmp(s, "PR1")==0) return PR1;
  else if(strcmp(s, "PR2")==0) return PR2;
  else if(strcmp(s, "FOLD")==0) return FOLD;
  else if(strcmp(s, "IND")==0) return IND;
  else if(strcmp(s, "FWD")==0) return FWD;
  else if(strcmp(s, "INT")==0) return INT;
  else{
    fprintf(stderr, "strToH failed\n");
    exit(-1);
  }
}

enum subop strToSubop(char* s){
  if(strcmp(s, "r+")==0) return RPLUS;
  else if(strcmp(s, "imm")==0) return IMM;
  else if(strcmp(s, "x")==0) return X;
  else if(strcmp(s, "c[]")==0) return CLO;
  else if(strcmp(s, "addr")==0) return ADDR;
  else{
    fprintf(stderr, "strToSubop failed\n");
    exit(-1);
  }
}

/*
generator syntax:
4
print3 H r+ c[] imm 2 3 4
print1 H x 0
copyx
copyc 9
*/

struct sizedGen loadGenerator(char* path){
  FILE* file;
  int size;
  int i;

  char buf[256];

  int tmp0, tmp1, tmp2;
  enum subop subop0, subop1, subop2;
  enum H tmpH;

  file = fopen(path,"r");
  if(file == NULL){
    fprintf(stderr, "can't open generator file\n");
    exit(-1);
  }

  if(fscanf(file, "%d\n", &size) < 1){
    fprintf(stderr, "error loading generator\n");
    exit(-1);
  }

  struct genIn* codes = malloc(size * sizeof(struct genIn));

  for(i=0; i<size; i++){
    if(fscanf(file, "%s ", buf) < 1){
      fprintf(stderr, "bad line\n");
      exit(-1);
    }
    if(strcmp(buf,"print1")==0){
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad head symbol\n"); exit(-1); }
      tmpH = strToH(buf);
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad subop\n"); exit(-1); }
      subop0 = strToSubop(buf);
      if(fscanf(file, "%d\n", &tmp0) < 1){ fprintf(stderr, "bad number\n"); exit(-1); }
      codes[i].type = PRINT1;
      codes[i].K = tmpH;
      codes[i].sub[0] = subop0;
      codes[i].pay[0] = tmp0;
    }
    else if(strcmp(buf,"print2")==0){
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad head symbol\n"); exit(-1); }
      tmpH = strToH(buf);
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad subop\n"); exit(-1); }
      subop0 = strToSubop(buf);
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad subop\n"); exit(-1); }
      subop1 = strToSubop(buf);
      if(fscanf(file, "%d\n", &tmp0) < 1){ fprintf(stderr, "bad number\n"); exit(-1); }
      if(fscanf(file, "%d\n", &tmp1) < 1){ fprintf(stderr, "bad number\n"); exit(-1); }
      codes[i].type = PRINT2;
      codes[i].K = tmpH;
      codes[i].sub[0] = subop0;
      codes[i].sub[1] = subop1;
      codes[i].pay[0] = tmp0;
      codes[i].pay[1] = tmp1;
    }
    else if(strcmp(buf,"print3")==0){
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad head symbol\n"); exit(-1); }
      tmpH = strToH(buf);
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad subop\n"); exit(-1); }
      subop0 = strToSubop(buf);
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad subop\n"); exit(-1); }
      subop1 = strToSubop(buf);
      if(fscanf(file, "%s ", buf) < 1){ fprintf(stderr, "bad subop\n"); exit(-1); }
      subop2 = strToSubop(buf);
      if(fscanf(file, "%d\n", &tmp0) < 1){ fprintf(stderr, "bad number\n"); exit(-1); }
      if(fscanf(file, "%d\n", &tmp1) < 1){ fprintf(stderr, "bad number\n"); exit(-1); }
      if(fscanf(file, "%d\n", &tmp2) < 1){ fprintf(stderr, "bad number\n"); exit(-1); }
      codes[i].type = PRINT3;
      codes[i].K = tmpH;
      codes[i].sub[0] = subop0;
      codes[i].sub[1] = subop1;
      codes[i].sub[2] = subop2;
      codes[i].pay[0] = tmp0;
      codes[i].pay[1] = tmp1;
      codes[i].pay[2] = tmp2;
    }
    else if(strcmp(buf,"copyx")==0){
      codes[i].type = COPYX;
    }
    else if(strcmp(buf,"copyc")==0){
      if(fscanf(file, "%d\n", &tmp0) < 1){
        fprintf(stderr, "bad copyc instruction\n");
        exit(-1);
      }
      codes[i].type = COPYC;
      codes[i].pay[0] = tmp0;
    }
    else{
      fprintf(stderr, "bad opcode\n");
      exit(-1);
    }
  }

  fclose(file);

  struct sizedGen g = {size, codes};
  return g;
}


// Garbage Collector

// forward declaration for mutual recursion
struct obj* gcLoop(struct obj* this, struct runtime* rts);

// this has already been moved, you just need to fixup its components.
// also, this is guaranteed NOT to be a "fat" lambda node
void gcThin(struct obj* this, struct runtime* rts){
  switch(this->h){
    case PR1:
    case PR2:
    case S:
    case IND:
    case PACK:
      this->com[0].ptr = gcLoop(this->com[0].ptr, rts);
      break;
    case P:
    case AT:
    case CONS:
    case BIND:
    case SEQ:
      this->com[0].ptr = gcLoop(this->com[0].ptr, rts);
      this->com[1].ptr = gcLoop(this->com[1].ptr, rts);
      break;
    case IF:
    case ITER:
    case FOLD:
      this->com[0].ptr = gcLoop(this->com[0].ptr, rts);
      this->com[1].ptr = gcLoop(this->com[1].ptr, rts);
      this->com[2].ptr = gcLoop(this->com[2].ptr, rts);
      break;
    case DO:
      this->com[1].ptr = gcLoop(this->com[1].ptr, rts);
      break;
    case LAM: // do nothing
    case UNIT:
    case T:
    case F:
    case NIL:
    case Z:
    case INT:
    case FWD:
      break;
  }
}

struct obj* gcLoop(struct obj* this, struct runtime* rts){
  if(this->h == UNIT){ return &rts->unit; }
  if(this->h == T){    return &rts->tt; }
  if(this->h == F){    return &rts->ff; }
  if(this->h == NIL){  return &rts->nil; }
  if(this->h == Z){    return &rts->zero; }

  //if this is an already moved node, return the forwarding pointer
  if(this->h == FWD){ return this->com[0].ptr; }
  
  //otherwise move to new heap and update original with forwarding pointer
  struct obj* that = cloneObj(this, rts);
  this->h = FWD;
  this->com[0].ptr = that;

  // "fat lambda" node needs special care
  int lamSize = that->com[0].i;
  if(that->h == LAM && lamSize > 0){
    if(this->com[2].ptr->h == FWD){//shared closure already moved
      that->com[2] = this->com[2];
    }
    else{
      struct obj* clo = cloneClosure(that->com[2].ptr, lamSize, rts);
      that->com[2].ptr->h = FWD;
      that->com[2].ptr->com[0].ptr = clo;
      that->com[2].ptr = clo;
      int i;
      for(i=0; i < lamSize; i++){ gcThin(&clo[i], rts); }
    }
  }
  else{
    gcThin(that, rts);
  }

  return that;
}

void swapHeaps(struct runtime* rts){
  struct obj* tmp = rts->heap;
  rts->heap = rts->oldHeap;
  rts->oldHeap = tmp;
}

void gc(struct runtime* rts){
  swapHeaps(rts);
  rts->heapPtr = 5; // magic, don't mess up atomic symbols
  rts->root = gcLoop(rts->root, rts);

  //fix the stack
  int i;
  for(i=0;i<rts->stackPtr;i++) rts->stack[i] = rts->stack[i]->com[0].ptr;

  //fix cursor if any
  if(rts->cursor) rts->cursor = rts->cursor->com[0].ptr;
}

void growHeaps(struct runtime* rts, int newSize){
  struct obj* tmp;

  tmp = realloc(rts->oldHeap, newSize * sizeof(struct obj));
  if(tmp == NULL){
    fprintf(stderr, "failed to grow heap1 (%s)\n", strerror(errno));
    exit(-1);
  }

  rts->oldHeap = tmp;

  gc(rts);

  tmp = realloc(rts->oldHeap, newSize * sizeof(struct obj));
  if(tmp == NULL){
    fprintf(stderr, "failed to grow heap1 (%s)\n", strerror(errno));
    exit(-1);
  }

  rts->oldHeap = tmp;
  rts->heapSize = newSize;
}


// Entry point to GC. Usually this returns without doing anything.
// if amount is not available, it does a compaction and possibly heap
// expansion. In any case it also fixes references on the stack.
struct obj* reserve(int amount, struct obj* cur, struct runtime* rts){
  if(rts->heapPtr + amount < rts->heapSize - 1) return cur;

  rts->cursor = cur;
  gc(rts);

  if(rts->heapPtr + amount < rts->heapSize - 1){
    int newSize = 4096;
    while(!(rts->heapPtr + amount < newSize - 1)) newSize *= 2;
    growHeaps(rts, newSize);
  }

  cur = rts->cursor;
  rts->cursor = NULL;
  return cur;
}



// Interpreter
//
// Actually there are two interpreters. One for the generator language
// one for the heap language.

struct obj* runGenerator(
  struct obj* x,
  struct obj clo[],
  struct sizedGen sg,
  struct runtime* rts
){
  ucom tmp[3];
  int i,j;
  struct obj* target = rts->heap + rts->heapPtr;
  int n = sg.size;
  struct genIn* gi;
  for(i=0; i<n; i++){
    gi = sg.code + i;
    switch(gi->type){
      case COPYX: cloneObj(x,rts); break;
      case COPYC: cloneObj(&clo[gi->pay[0]], rts); break;
      case PRINT1:
        switch(gi->sub[0]){
          case RPLUS:  tmp[0].ptr = target+gi->pay[0]; break;
          case IMM:    tmp[0].i   = gi->pay[0]; break;
          case X:      tmp[0].ptr = x; break;
          case CLO:    tmp[0].ptr = &clo[gi->pay[0]]; break;
          case ADDR:   tmp[0].ptr = rts->heap + gi->pay[0]; break;
          default: fprintf(stderr, "bad generator subinstruction 1\n"); exit(-1); break;
        }
        put1(gi->K, tmp[0], rts);
        break;
      case PRINT2:
        for(j=0; j<2; j++){
          switch(gi->sub[j]){
            case RPLUS: tmp[j].ptr = target+gi->pay[j]; break;
            case IMM:   tmp[j].i   = gi->pay[j]; break;
            case X:     tmp[j].ptr = x; break;
            case CLO:   tmp[j].ptr = &clo[gi->pay[j]]; break;
            case ADDR:  tmp[j].ptr = rts->heap + gi->pay[j]; break;
            default: fprintf(stderr, "bad generator subinstruction 2\n"); exit(-1); break;
          }
        }
        put2(gi->K, tmp[0], tmp[1], rts);
        break;
      case PRINT3:
        for(j=0; j<3; j++){
          switch(gi->sub[j]){
            case RPLUS: tmp[j].ptr = target+gi->pay[j]; break;
            case IMM:   tmp[j].i   = gi->pay[j]; break;
            case X:     tmp[j].ptr = x; break;
            case CLO:   tmp[j].ptr = &clo[gi->pay[j]]; break;
            case ADDR:  tmp[j].ptr = rts->heap + gi->pay[j]; break;
            default: fprintf(stderr, "bad generator subinstruction 3\n"); exit(-1); break;
          }
        }
        put3(gi->K, tmp[0], tmp[1], tmp[2], rts);
        break;
      default: fprintf(stderr, "bad generator instruction\n"); exit(-1);
    }
  }

  return target;
}



void crash(char* msg){
  fprintf(stderr, "crunch crashed (%s)\n", msg);
  exit(-1);
}

// evaluate a chosen heap term until you get a value (if ever)
struct obj* crunch(struct obj* start, struct runtime* rts){

  struct obj* cur = start;
  struct obj* answer = NULL;
  int m;
  struct ffi* ffi;
  int dontExec = 0; // dontExec > 0, BIND is a value. otherwise, BIND is a dtor

  for(;;){
    //value?
    if(isVal(cur,dontExec)){
      if(rts->stackPtr == 0) return cur;
      answer = cur;
      cur = pop(rts);
      continue;
    }

    //indirection?
    if(cur->h == IND){
      cur = cur->com[0].ptr;
      continue;
    }

    if(cur->h == FWD) crash("FWD found in live heap");

    //if it's not a value, IND, or FWD, it must be a destructor

    //can't necessarily destruct
    if(answer == NULL){
      push(cur, rts);
// this check could be made redundant by always putting scrutinee first
      switch(cur->h){
        case PR1:
        case PR2:
        case AT:
        case BIND:
        case PACK:
          cur = cur->com[0].ptr;
          continue;
        case SEQ:
          cur = cur->com[0].ptr;
          dontExec++;
          continue;
        case ITER:
        case IF:
        case FOLD:
          cur = cur->com[2].ptr;
          continue;
        default: crash("bad destructor");
      }
    }

    //after this point, answer (value of scrutinee) is available

    //PACK and SEQ
    if(cur->h == PACK){
      //pack(Z,i) = int(i)
      //pack(S n, i) = pack(n, i+1);
      //pack(int(j), i) = int(j + i);
      switch(cur->com[0].ptr->h){
        case Z:
          cur->h = INT;
          cur->com[0].i = cur->com[1].i;
          break;
        case S:
          cur->com[1].i++;
          cur->com[0]= cur->com[0].ptr->com[0];
        case INT:
          cur->h = INT;
          cur->com[0].i = cur->com[1].i + cur->com[0].ptr->com[0].i;
          break;
        default: crash("ctor/dtor mismatch (PACK)");
      }
      continue;
    }

    if(cur->h == SEQ){
      //seq(val,b) = b
      *(cur) = *(cur->com[1].ptr);
      dontExec--;
      continue;
    }

    //matching destructor, do destruct
    if(answer->h == P){
      //make sure to replace dtor node with result
      switch(cur->h){
        case PR1: *cur = *(answer->com[0].ptr); break;
        case PR2: *cur = *(answer->com[1].ptr); break;
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == IF){
      //cur->com[2].ptr = answer;
      switch(answer->h){
        case F: *cur = *(cur->com[0].ptr); break;
        case T: *cur = *(cur->com[1].ptr); break;
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == ITER){
      //cur->com[2].ptr = answer;
      switch(answer->h){
        case Z: *cur = *(cur->com[0].ptr); break;
        case S:
          cur = reserve(1,cur,rts);
          ucom b = cur->com[0];
          ucom f = cur->com[1];
          ucom n = cur->com[2].ptr->com[0];
          // iter(b,f,S n) = f @ iter(b,f,n)
          cur->h = AT;
          cur->com[0] = f;
          cur->com[1] = put3u(ITER,b,f,n, rts);
          break;
        case INT:
          m = answer->com[0].i;
          if(m <= 0){
            *cur = *(cur->com[0].ptr);
          }
          else{ // iter(b,f,int(n)) = f @ iter(b,f,int(n-1))
            cur = reserve(2,cur,rts);
            ucom b = cur->com[0];
            ucom f = cur->com[1];
            ucom um = {.i = m-1 };
            cur->h = AT;
            cur->com[0] = f;
            cur->com[1] = put3u(ITER, b, f, put1u(INT,um,rts),rts);
            break;
          }
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == FOLD){
      //cur->com[2].ptr = answer;
      switch(answer->h){
        case NIL: *cur = *(cur->com[0].ptr); break;
        case CONS:
          cur = reserve(2,cur,rts);
          struct obj* b = cur->com[0].ptr;
          struct obj* f = cur->com[1].ptr;
          struct obj* x = cur->com[2].ptr->com[0].ptr;
          struct obj* xs = cur->com[2].ptr->com[1].ptr;
          // fold(b,f,x:xs) = (f @ x) @ fold(b,f,xs)
          cur->h = AT;
          cur->com[0].ptr = put2p(AT,f,x,rts);
          cur->com[1].ptr = put3p(FOLD,b,f,xs,rts);
          break;
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == AT){
      //cur->com[0].ptr = answer;
      if(answer->h != LAM) crash("dtor-ctor mismatch LAM/AT");
      cur = reserve(answer->com[0].i, cur, rts);
      struct obj* body = runGenerator(
        cur->com[1].ptr, // argument
        cur->com[0].ptr->com[2].ptr, // closure
        generators[cur->com[0].ptr->com[1].i],
        rts
      );
      cur->h = IND;
      cur->com[0].ptr = body;
      answer = NULL;
      continue;
    }

    // BIND is a dtor unless dontExec > 0
    // this happens when evaluating an IO action inside SEQ
    // an IO action can't be the scrutinee of any other dtor so we don't have
    // to worry about executing I/O accidentally in other situations.
    if(cur->h == BIND){
      if(answer->h != DO) crash("dtor-ctor mismatch DO/BIND");
      // DO ffi x >>= k   ==>  ffi(x,k)
      ffi = &ffiBindings[answer->com[0].i];
      // reserve an amount of space that depends on the FFI action
      cur = reserve(ffi->spaceNeeded, cur, rts);
      cur = ffi->execute(
        cur->com[0].ptr->com[1].ptr, // x
        cur->com[1].ptr,             // k
        rts
      );
      answer = NULL;
      continue;
    }

    crash("bad node");

  }

}

// putc(c) >>= k  = *output c*, k ()
struct obj* ioPutC(struct obj* x, struct obj* k, struct runtime* rts){

  if(x->h == INT){
    fputc(x->com[0].i, stdout);
    return put2p(AT,k,&rts->unit,rts);
  }
  else{
    rts->stuckReason = FFI_ARGUMENT_ERROR;
    return NULL;
  }

}

struct obj* ioGetC(struct obj* x, struct obj* k, struct runtime* rts){
  int c = fgetc(stdin);

  if(c==EOF && feof(stdin)){
    // FIXME exception
    fprintf(stderr, "getc: EOF\n");
    exit(-1);
  }
  else if(c==EOF && ferror(stdin)){
    // FIXME exception
    fprintf(stderr, "%s\n", strerror(errno));
    exit(-1);
  }

  return put2p(AT,k, put1i(INT, c, rts), rts);
}

struct obj* ioExit(struct obj* x, struct obj* ignore, struct runtime* rts){
  rts->stuckReason = FFI_EXIT;
  return &rts->unit;
}

struct obj* ioRaise(struct obj* ex, struct obj* ignore, struct runtime* rts){
  //raise(ex)
  //hand = popEx();
  //hand(ex)
  struct obj* hand = popExStack(rts); //never empty
  return put2p(AT,hand,ex,rts);
}

struct obj* ioCatch(struct obj* pair, struct obj* k, struct runtime* rts){
  //catch(act, h) >>= k
  //  =  push(\ex -> h(ex) >>= return)
  //     (act >>= \x -> pop >>= \_ -> return x) >>= k
  //throw ex >>= _
  //  =  hand <- pop
  //     
  struct obj* act = pair->com[0].ptr->com[0].ptr;
  struct obj* h   = pair->com[0].ptr->com[1].ptr;
  // push(\ex -> h ex >>= k)
  struct obj* hand = mkHandler(h, k, rts); // needs to allocate 2 AT nodes
  pushExStack(hand, rts);
  return mkFrame(act, k, rts); // (act >>= \x -> pop >> k x)
}

// inserted by the execution of ioCatch
struct obj* ioUncatch(struct obj* x, struct obj* k, struct runtime* rts){
  popExStack(rts);
  return put2p(AT, k, &rts->unit, rts);
}


int main(){
  int c;
  int counter;
  struct obj* tmp;

  struct runtime* rts;
  rts->stackSize = 4096;
  rts->stack = malloc(rts->stackSize * sizeof(struct obj*));
  rts->stackPtr = 0;
  rts->heapSize = 4096;
  rts->heap = malloc(rts->heapSize * sizeof(struct obj));
  rts->oldHeap = malloc(rts->heapSize * sizeof(struct obj));
  rts->heapPtr = 0;

  // initialize heaps with magic atomic values
  rts->unit.h = UNIT;
  rts->tt.h = T;
  rts->ff.h = F;
  rts->nil.h = NIL;
  rts->zero.h = Z;

  // test data
  put2p(AT,
    put2p(LAM,&rts->zero,&rts->zero,rts),
    &rts->unit,
    rts
  ); // (\ 0 0) @ UNIT
  rts->root = rts->heap + 6;

  // load generator file
  struct sizedGen sg = loadGenerator("mygen");
  // register generator in position g0
  generators[0] = sg;

  printHeap(rts);

  crunch(rts->root, rts);

  return 0;
    

}




// graph machine notes
// basically this machine has these components
// - heap x2
// - stack
// - root
// - cursor
// - answer
// - generators
//
// the interpreter algorithm (crunch) contains several hard coded destruct
// rules which vary in terms of memory-use, decision making, result sourcing,
// and in the case of iter, access of primitives.
//
// the i/o driver has three hard coded behaviors, one for each I/O primitive.
// this implements the i/o loop.
//
// the generator language can currently adapt to changes in the data language.
// it may need to be updated if certain primitives are added.
//
// improvement1: allow custom destruct rules. implement existing rules in terms
// of the custom destruct language.
//
// improvement2: allow more general i/o. implement existing i/o in terms of
// the custom i/o language. allow i/o to be mocked.
//
// improvement3: move the machine bits from global scope into a struct so you
// can have multiple interpreters running concurrently.
//
// improvement4:
//  provide access to more primitives data types like ints, floats, arrays,
//  packed records, mutable cells
//
// improvement0:
//   write tests of all the existing generation instructions and data nodes
//
// improvement5: add exceptions for things like IO errors
// improvement6: some kind of "stack trace"


// destruct rules, generalizations
// pr1(P x y) = x                    pick component
// pr2(P x y) = y                    
// if(x,y,F) = x                     pick component depending on scrutinee
// if(x,y,T) = y
// iter(b,f,Z) = b                   pick component depending on scrutinee
// iter(b,f,S n) = f iter(b,f,n)     recursion on component
// fold(b,f,NIL) = b
// fold(b,f,x:xs) = f x fold(b,f,xs) recursion on component
// (LAM n g)[ci] @ x = g(x,ci)       generator based
// all but 1 of these can be implemented with the destruct rule for W-types.
//
// i/o generalizations
// INPUT k         get data, decode data, apply handler
// OUTPUT c k      encode/crunch argument, execute and ignore, run k
// EXIT            execute effect, not expected to return
// so we are expecting certain data values to be convertible to foreign
// data. then we are expecting to decode foreign data results.
// We might also want multiple continuations, like in case of exception
// handling. might want to do i/o actions in dedicated threads and interleave
// processes in another thread.