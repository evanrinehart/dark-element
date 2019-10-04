#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

// C program which continually applies the evaluation rule

enum H
  {STAR,T,F,Z,NIL,S,P,CONS,INT,INPUT,OUTPUT,EXIT,LAM,
  IF,ITER,AT,PR1,PR2,FOLD,
  IND,FWD};
// other things... ADDR, DOUBLE, BUFFER, CELL, VECTOR

enum GI {COPYX, COPYC, PRINT1, PRINT2, PRINT3};
enum subop {RPLUS, IMM, X, CLO, ADDR};

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

struct sizedGen {
  int size;
  struct genIn* code;
};

struct sizedGen generators[4096];

int heapSize = 4096;
struct obj* heap1;
struct obj* heap2;
struct obj* heap;
struct obj* root;
struct obj* cursor;
int heapPtr = 0;
struct obj* star;
struct obj* tt;
struct obj* ff;
struct obj* nil;
struct obj* zero;

int stackSize = 256;
struct obj** stack;
int stackPtr;


int isVal(struct obj* o){
  if(o->h <= LAM) return 1;
  else            return 0;
}



// Stack and Heap operations

void growStack(){
  stackSize *= 2;
  struct obj** tmp;
  tmp = realloc(stack, stackSize * sizeof(struct obj*));
  if(tmp == NULL){
    fprintf(stderr, "failed to grow stack (%s)\n", strerror(errno));
    exit(-1);
  }
  stack = tmp;
}

void growHeaps(){
  heapSize *= 2;
  struct obj* tmp;
  int which = heap==heap1 ? 1 : 2;

  tmp = realloc(heap1, heapSize * sizeof(struct obj));
  if(tmp == NULL){
    fprintf(stderr, "failed to grow heap1 (%s)\n", strerror(errno));
    exit(-1);
  }
  heap1 = tmp;

  tmp = realloc(heap2, heapSize * sizeof(struct obj));
  if(heap2==NULL){
    fprintf(stderr, "failed to grow heap2 (%s)\n", strerror(errno));
    exit(-1);
  }
  heap2 = tmp;

  heap = which==1 ? heap1 : heap2;
}

void push(struct obj* ptr){
  if(stackPtr+1 == stackSize) growStack();
  stack[stackPtr] = ptr;
  stackPtr++;
}

struct obj* pop(){
  if(stackPtr == 0){
    fprintf(stderr, "stack underflow\n");
    exit(-1);
  }
  stackPtr--;
  return stack[stackPtr];
}

struct obj* put0(enum H h){
  struct obj o = {h};
  struct obj* ptr = heap + heapPtr;
  heap[heapPtr] = o;
  heapPtr++;
  return ptr;
}

struct obj* put1(enum H h, ucom x){
  struct obj o = {h,{x}};
  struct obj* ptr = heap + heapPtr;
  heap[heapPtr] = o;
  heapPtr++;
  return ptr;
}

ucom put1u(enum H h, ucom x){
  struct obj* o = put1(h,x);
  ucom v = {.ptr = o};
  return v;
}

struct obj* put2(enum H h, ucom x, ucom y){
  struct obj o = {h,{x,y}};
  struct obj* ptr = heap + heapPtr;
  heap[heapPtr] = o;
  heapPtr++;
  return ptr;
}

ucom put2u(enum H h, ucom x, ucom y){
  struct obj* o = put2(h,x,y);
  ucom v = {.ptr = o};
  return v;
}


struct obj* put3(enum H h, ucom x, ucom y, ucom z){
  struct obj o = {h,{x,y,z}};
  struct obj* ptr = heap + heapPtr;
  heap[heapPtr] = o;
  heapPtr++;
  return ptr;
}

ucom put3u(enum H h, ucom x, ucom y, ucom z){
  struct obj* o = put3(h,x,y,z);
  ucom v = {.ptr = o};
  return v;
}

struct obj* cloneObj(struct obj* orig){
  struct obj* ptr = heap + heapPtr;
  heap[heapPtr] = *orig;
  heapPtr++;
  return ptr;
}



// Printers So We Can Tell What's Going On

#define REL(o,i) (o->com[i].ptr - heap)

void printObj(struct obj* o){
  switch(o->h){
    case STAR: printf("○\b●\n"); return;
    case T:    printf("T\n"); return;
    case F:    printf("F\n"); return;
    case Z:    printf("Z\n"); return;
    case S:    printf("S %ld\n",REL(o,0)); return;
    case P:    printf("P %ld %ld\n",REL(o,0),REL(o,1)); return;
    case NIL:  printf("NIL\n"); return;
    case EXIT: printf("EXIT\n"); return;
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
    case INPUT: printf("INPUT %ld\n",REL(o,0)); return;
    case OUTPUT: printf("OUTPUT %ld %ld\n",REL(o,0),REL(o,1)); return;
    case INT:  printf("INT %d\n", o->com[0].i); return;
  }
}

void printK(enum H k){
  switch(k){
    case STAR: printf("STAR "); return;
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
    case EXIT: printf("EXIT "); return;
    case INPUT: printf("INPUT "); return;
    case OUTPUT: printf("OUTPUT "); return;
    case INT: printf("INT "); return;
  }
}

void printHeap(){
  int i;
  char num[16];
  int a = 0;
  int b = heapPtr;
  int digits = 0;
  int tmp = b;
  while(tmp > 0){ digits++; tmp /= 10; }
  digits = digits < 1 ? 1 : digits;
  digits += 2;

  for(i=a; i<b; i++){
    if(heap+i==root) printf("> ");
    else printf("  ");
    sprintf(num,"%d.",i);
    printf("%-*s ",digits,num);
    printObj(heap+i);
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
  if(strcmp(s, "STAR")==0) return STAR;
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
  else if(strcmp(s, "INPUT")==0) return INPUT;
  else if(strcmp(s, "OUTPUT")==0) return OUTPUT;
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
struct obj* gcLoop(struct obj* this);

// this has already been moved, you just need to fixup its components.
// also, this is guaranteed NOT to be a "fat" lambda node
void gcThin(struct obj* this){
  switch(this->h){
    case PR1:
    case PR2:
    case S:
    case IND:
      this->com[0].ptr = gcLoop(this->com[0].ptr);
      break;
    case P:
    case AT:
    case CONS:
      this->com[0].ptr = gcLoop(this->com[0].ptr);
      this->com[1].ptr = gcLoop(this->com[1].ptr);
      break;
    case IF:
    case ITER:
    case FOLD:
      this->com[0].ptr = gcLoop(this->com[0].ptr);
      this->com[1].ptr = gcLoop(this->com[1].ptr);
      this->com[2].ptr = gcLoop(this->com[2].ptr);
      break;
    default:
      break;
  }
}

struct obj* gcLoop(struct obj* this){
  // annoying magic locations of atomic symbols
  if(this->h == STAR){ return heap+0; }
  if(this->h == T){    return heap+1; }
  if(this->h == F){    return heap+2; }
  if(this->h == NIL){  return heap+3; }
  if(this->h == Z){    return heap+4; }

  //if this is an already moved node, return the forwarding pointer
  if(this->h == FWD){ return this->com[0].ptr; }
  
  //otherwise move to new heap and update original with forwarding pointer
  struct obj* that = cloneObj(this);
  this->h = FWD;
  this->com[0].ptr = that;

  // "fat lambda" node needs special care
  int lamSize = that->com[0].i;
  if(that->h == LAM && lamSize > 0){
    int i;
    for(i=0; i < lamSize; i++){ cloneObj(this+1+i); }
    for(i=0; i < lamSize; i++){ gcThin(that+1+i); }
  }
  else{
    gcThin(that);
  }

  return that;
}


// Entry point to GC. Usually this returns without doing anything.
// if amount is not available, it does a compaction and possibly heap
// expansion. In any case it also fixes references on the stack and returns
// a corrected cursor.
struct obj* reserve(int amount, struct obj* cursor){
  if(heapPtr + amount < heapSize - 1) return cursor;

  //compact the heap, invalidates any local pointers into heap
  heap = heap==heap1 ? heap2 : heap1;
  heapPtr = 5; // magic, don't mess up atomic symbols
  root = gcLoop(root);

  //expand heaps until we really have enough space
  while(amount >= heapSize - heapPtr) growHeaps();

  //fix the stack
  int i;
  for(i=0;i<stackPtr;i++) stack[i] = stack[i]->com[0].ptr;

  //return fixed cursor (don't fix if root)
  return cursor==root ? root : cursor->com[0].ptr;
}



// Interpreter
//
// Actually there are two interpreters. One for the generator language
// one for the heap language.

struct obj* runGenerator(struct obj* x, struct obj clo[], struct sizedGen sg){
  ucom tmp[3];
  int i,j;
  struct obj* target = heap + heapPtr;
  int n = sg.size;
  struct genIn* gi;
  for(i=0; i<n; i++){
    gi = sg.code + i;
    switch(gi->type){
      case COPYX: cloneObj(x); break;
      case COPYC: cloneObj(&clo[gi->pay[0]]); break;
      case PRINT1:
        switch(gi->sub[0]){
          case RPLUS:  tmp[0].ptr = target+gi->pay[0]; break;
          case IMM:    tmp[0].i   = gi->pay[0]; break;
          case X:      tmp[0].ptr = x; break;
          case CLO:    tmp[0].ptr = &clo[gi->pay[0]]; break;
          case ADDR:   tmp[0].ptr = heap + gi->pay[0]; break;
          default: fprintf(stderr, "bad generator subinstruction 1\n"); exit(-1); break;
        }
        put1(gi->K, tmp[0]);
        break;
      case PRINT2:
        for(j=0; j<2; j++){
          switch(gi->sub[j]){
            case RPLUS: tmp[j].ptr = target+gi->pay[j]; break;
            case IMM:   tmp[j].i   = gi->pay[j]; break;
            case X:     tmp[j].ptr = x; break;
            case CLO:   tmp[j].ptr = &clo[gi->pay[j]]; break;
            case ADDR:  tmp[j].ptr = heap + gi->pay[j]; break;
            default: fprintf(stderr, "bad generator subinstruction 2\n"); exit(-1); break;
          }
        }
        put2(gi->K, tmp[0], tmp[1]);
        break;
      case PRINT3:
        for(j=0; j<3; j++){
          switch(gi->sub[j]){
            case RPLUS: tmp[j].ptr = target+gi->pay[j]; break;
            case IMM:   tmp[j].i   = gi->pay[j]; break;
            case X:     tmp[j].ptr = x; break;
            case CLO:   tmp[j].ptr = &clo[gi->pay[j]]; break;
            case ADDR:  tmp[j].ptr = heap + gi->pay[j]; break;
            default: fprintf(stderr, "bad generator subinstruction 3\n"); exit(-1); break;
          }
        }
        put3(gi->K, tmp[0], tmp[1], tmp[2]);
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
struct obj* crunch(struct obj* start){

  struct obj* cur = start;
  struct obj* answer = NULL;
  int m;

  //the stack should start empty
  if(stackPtr != 0) crash("crunch expects an empty stack\n");

  for(;;){
    //value?
    if(isVal(cur)){
      if(stackPtr == 0) return cur;
      answer = cur;
      cur = pop();
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
      push(cur);
// this check could be made redundant by always putting scrutinee first
      switch(cur->h){
        case PR1:
        case PR2:
        case AT:
          cur = cur->com[0].ptr;
          continue;
        case ITER:
        case IF:
        case FOLD:
          cur = cur->com[2].ptr;
          continue;
        default: crash("bad destructor");
      }
    }

    //matching destructor, do destruct
    if(answer->h == P){
      cur->com[0].ptr = answer;
      switch(cur->h){
        case PR1: cur = answer->com[0].ptr; break;
        case PR2: cur = answer->com[1].ptr; break;
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == IF){
      cur->com[2].ptr = answer;
      switch(answer->h){
        case F: cur = cur->com[0].ptr; break;
        case T: cur = cur->com[1].ptr; break;
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == ITER){
      cur->com[2].ptr = answer;
      switch(answer->h){
        case Z: cur = cur->com[0].ptr; break;
        case S:
          cur = reserve(2,cur);
          ucom b = cur->com[0];
          ucom f = cur->com[1];
          ucom n = cur->com[2].ptr->com[0];
          // iter(b,f,S n) = f @ iter(b,f,n)
          cur = put2(AT,f,put3u(ITER,b,f,n));
          break;
        case INT:
          m = answer->com[0].i;
          if(m <= 0){
            cur = cur->com[0].ptr;
          }
          else{ // iter(b,f,int(n)) = f @ iter(b,f,int(n-1))
            cur = reserve(3,cur);
            ucom b = cur->com[0];
            ucom f = cur->com[1];
            ucom um = {.i = m-1 };
            cur = put2(AT, f, put3u(ITER, b, f, put1u(INT,um)));
            break;
          }
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == FOLD){
      cur->com[2].ptr = answer;
      switch(answer->h){
        case NIL: cur = cur->com[0].ptr; break;
        case CONS:
          cur = reserve(3,cur);
          ucom b = cur->com[0];
          ucom f = cur->com[1];
          ucom x = cur->com[2].ptr->com[0];
          ucom xs = cur->com[2].ptr->com[1];
          // fold(b,f,x:xs) = (f @ x) @ fold(b,f,xs)
          cur = put2(AT,put2u(AT,f,x),put3u(FOLD,b,f,xs));
          break;
        default: crash("dtor-ctor mismatch");
      }
      answer = NULL;
      continue;
    }

    if(cur->h == AT){
      cur->com[0].ptr = answer;
      if(answer->h != LAM) crash("dtor-ctor mismatch LAM/AT");
      cur = reserve(answer->com[0].i, cur);
      cur = runGenerator(
        cur->com[1].ptr,
        cur->com[0].ptr + 1,
        generators[cur->com[0].ptr->com[1].i]
      );
      answer = NULL;
      continue;
    }

    crash("bad node");

  }

}


int main(){
  int c;
  int counter;
  struct obj* tmp;

  stack = malloc(stackSize * sizeof(struct obj*));
  stackPtr = 0;

  heap1 = malloc(heapSize * sizeof(struct obj));
  heap2 = malloc(heapSize * sizeof(struct obj));
  heap = heap1;
  heapPtr = 0;

  // initialize heaps with magic atomic values
  star = put0(STAR);
  tt   = put0(T);
  ff   = put0(F);
  nil  = put0(NIL);
  zero = put0(Z);

  int i;
  for(i=0; i<5; i++){ heap2[i] = heap1[i]; }

  // test data
  ucom uzero = {.i=0};
  ucom ustar = {.ptr=star};
  put2(AT,put2u(LAM,uzero,uzero),ustar); // (\ 0 0) @ STAR
  root = heap + 6;

  // load generator file
  struct sizedGen sg = loadGenerator("mygen");
  // register generator in position g0
  generators[0] = sg;

  printHeap();
  for(;;){
    //printf("\n*crunch*\n\n");
    root = crunch(root);
    //printHeap();

    switch(root->h){
      case EXIT:
        return 0;
      case INPUT:
        c = fgetc(stdin);
        if(c==EOF && feof(stdin)){
          return 0;
        }
        else if(c==EOF && ferror(stdin)){
          fprintf(stderr, "%s\n", strerror(errno));
          exit(-1);
        }

        // crunch com[0] until  ...
        tmp = crunch(root->com[0].ptr);
        root->com[0].ptr = tmp;

        // ... get a lambda. Apply it
        if(root->com[0].ptr->h == LAM){
          reserve(2, root);
          ucom uc = {.i = c};
          root = put2(AT,root->com[0],put1u(INT,uc));
        }
        else{
          fprintf(stderr, "bad input continuation\n");
          exit(-1);
        }
        break;

      case OUTPUT:
        counter = 0;

        // consume numeric nodes into counter
        for(;;){
          tmp = crunch(root->com[0].ptr);
          if(tmp->h == Z){
            fputc(counter, stdout);
            break;
          }
          else if(tmp->h == S){
            counter++;
            root->com[0] = tmp->com[0];
            continue;
          }
          else if(tmp->h == INT){
            counter += tmp->com[0].i;
            fputc(counter, stdout);
            break;
          }
        }

        root = root->com[1].ptr;
        break;
      default:
        printf("cur h = %d\n", root->h);
        printHeap();
        fprintf(stderr, "bad i/o\n");
        exit(-1);
    }

  }

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
