
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);


/* VARIABLES */

/* ECE552 Assignment 4 - BEGIN CODE */

/* wrapper structure for reservation stations */
typedef struct insn_struct
{
	instruction_t* insn;
	bool is_ready;
	bool has_fu;
	struct insn_struct* next;
}insn_struct;

/* adds the new instruction into the list returns the pointer to the new element */
insn_struct* add(insn_struct* head, instruction_t* insn)
{
   if (head == NULL) {
      return NULL;
   }

   insn_struct* node = (insn_struct*)malloc(sizeof(insn_struct));
	
   node->insn = insn;
   node->is_ready = false;
   node->has_fu= false;
   node->next = NULL;

   insn_struct* current = head;
	
   while(current->next != NULL) {
      current = current->next;
   }

   current->next = node;
   return node;
}

/* ECE552 Assignment 4 - END CODE */


//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;


/* ECE552 Assignment 4 - BEGIN CODE */

//reservation stations (each reservation station entry contains a pointer to an instruction plus some additional information added)
static insn_struct* reservINT = NULL;
static insn_struct* reservFP = NULL;

/* ECE552 Assignment 4 - END CODE */

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];


//the index of the last instruction fetched
static int fetch_index = 0;

/* ECE552 Assignment 4 - BEGIN CODE */

static bool fetch_completed = false;

/* ECE552 Assignment 4 - END CODE */

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/* ECE552 Assignment 4 - BEGIN CODE */

/* Helper functions */

/* removes the head value in the array 
	 returns the new head
*/
void remove_head()
{
   int i;

   for (i = 0; i < instr_queue_size-1; i++) {
      instr_queue[i] = instr_queue[i + 1];
   }

   instr_queue[i] = NULL;
}	

bool check_if_list_full(insn_struct* queue, int size)
{
	int i = 1;

	insn_struct* temp = queue;

	if (temp == NULL)
	{
		return false;
	}

	while (temp->next != NULL)
	{
		temp = temp->next;
		i++;
	} 
	
	if (i == size)
	{
		return true;
	}
	
	return false;
}

bool is_rs_available(enum md_opcode op)
{	
   if (USES_INT_FU(op)) {
      return !check_if_list_full(reservINT, RESERV_INT_SIZE);
   } else if (USES_FP_FU(op)) {
      return !check_if_list_full(reservFP, RESERV_FP_SIZE);
   }
	
   return false;
}

insn_struct* set_rs_available(enum md_opcode op, instruction_t* insn) {

   if (USES_INT_FU(op)) {
      /* if head pointer */
      if (reservINT == NULL) {
			 reservINT = (insn_struct*)malloc(sizeof(insn_struct));
			 reservINT->insn = insn;
			 reservINT->is_ready = false;
			 reservINT->has_fu= false;
			 reservINT->next = NULL;
				
	 		 return reservINT;
      } else {
	 				return add(reservINT, insn);
      }
   } else if (USES_FP_FU(op)) {
      if (reservFP == NULL) {
			 reservFP = (insn_struct*)malloc(sizeof(insn_struct));
			 reservFP->insn = insn;
			 reservFP->is_ready = false;
			 reservFP->has_fu = false;
			 reservFP->next = NULL;

			 return reservFP;
      } else {
	 				return add(reservFP, insn);
      }
   }
	
   return NULL;
}

bool set_fu_available(enum md_opcode op, instruction_t* insn)
{
	int i;

	if (USES_INT_FU(op))
	{
		for (i = 0; i < FU_INT_SIZE; i++)
		{
			if (fuINT[i] == NULL)
			{
				fuINT[i] = insn;
				return true;
			}
		}
	}

	else if (USES_FP_FU(op))
	{
		for (i = 0; i < FU_FP_SIZE; i++)
		{
			if (fuFP[i] == NULL)
			{
				fuFP[i] = insn;
				return true;
			}
		}
	}
	return false;
}



void print_insn(instruction_t* insn, char* text)
{
	printf("--------%s STARTING",text);
	printf("-------------\n\n");

  md_print_insn(insn->inst, insn->pc, stdout);
  myfprintf(stdout, "\t%d\t%d\t%d\t%d\n", 
    insn->tom_dispatch_cycle,
    insn->tom_issue_cycle,
    insn->tom_execute_cycle,
    insn->tom_cdb_cycle);

	printf("--------%s ENDING",text);
	printf("-------------\n\n");
}

void print_list(insn_struct* queue, char* text, int limit)
{
  int i = 0;

	printf("--------%s STARTING",text);
	printf("-------------\n\n");

	insn_struct* temp = queue;

  while (temp != NULL && i < limit)
  {
    md_print_insn(temp->insn->inst, temp->insn->pc, stdout);
    myfprintf(stdout, "\t%d\t%d\t%d\t%d\n", 
	    temp->insn->tom_dispatch_cycle,
	    temp->insn->tom_issue_cycle,
	    temp->insn->tom_execute_cycle,
	    temp->insn->tom_cdb_cycle);
   	i++;
		temp =  temp->next;
  }

	printf("--------%s ENDING",text);
	printf("-------------\n\n");
}


void set_dependent_insn(insn_struct* insn) {

   int i;
   bool is_ready = true;

   for (i=0; i<3; i++) {
     if (insn->insn->r_in[i] != DNA) {
			 if (map_table[insn->insn->r_in[i]] == NULL) {
					is_ready &= true; 
			 } else {
				  is_ready = false;
					insn->insn->Q[i] = map_table[insn->insn->r_in[i]];
			 }
     }
   }

   insn->is_ready = is_ready;
}

/* ECE552 Assignment 4 - END CODE */

/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(instruction_trace_t* trace, counter_t sim_insn) {


  if(trace->next == NULL && fetch_index == trace->size - 1)
	{
			if(reservINT != NULL)
			{
				return false;
			}

			if(reservFP != NULL)
			{
				return false;
			}

		return true;
	}

	return false;

	/* ECE552 Assignment 4 - END CODE */
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

	/* ECE552 Assignment 4 - BEGIN CODE */

  if (commonDataBus != NULL && commonDataBus->tom_cdb_cycle != 0 && commonDataBus->tom_cdb_cycle < current_cycle)
	{
		int i;

		for (i = 0; i < 2; i++)
		{
			if (commonDataBus->r_out[i] != DNA)
			{
				map_table[commonDataBus->r_out[i]] = NULL;
			}
		}

		insn_struct* tempINT = reservINT;

		while (tempINT != NULL)
		{
			for (i = 0; i < 3; i++)
			{
				if (tempINT->insn != NULL && tempINT->insn->Q[i] == commonDataBus)
				{
					tempINT->insn->Q[i] = NULL;
				}
			}
			
			tempINT = tempINT->next;
		}

		tempINT = NULL;

		insn_struct* tempFP = reservFP;

		while (tempFP != NULL)
		{
			for (i = 0; i < 3; i++)
			{
				if (tempFP->insn != NULL && tempFP->insn->Q[i] == commonDataBus)
				{
					tempFP->insn->Q[i] = NULL;
				}
			}
			
			tempFP = tempFP->next;
		}

		tempFP = NULL;
		
		commonDataBus = NULL;
	}

	/* ECE552 Assignment 4 - END CODE */
}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

	/* ECE552 Assignment 4 - BEGIN CODE */

	int i;

	for (i = 0; i < FU_INT_SIZE; i++)
	{
		if (fuINT[i] != NULL && fuINT[i]->tom_execute_cycle + FU_INT_LATENCY <= current_cycle)
		{
			insn_struct* currentINT = reservINT;
			insn_struct* prevINT = NULL;

			while (currentINT != NULL)
			{
				if (fuINT[i] == currentINT->insn)
				{
					if (prevINT == NULL)
					{
						/* is the head of list */
						if (WRITES_CDB(currentINT->insn->op))
						{
							commonDataBus = currentINT->insn;
							commonDataBus->tom_cdb_cycle = current_cycle;
						}

						reservINT = currentINT->next;
						currentINT->insn = NULL;
						free(currentINT);
						currentINT = NULL;
						break;
					}
					else
					{
						if (WRITES_CDB(currentINT->insn->op))
						{
							commonDataBus = currentINT->insn;
							commonDataBus->tom_cdb_cycle = current_cycle;
						}

						prevINT->next = currentINT->next;
						currentINT->insn = NULL;
						free(currentINT);
						currentINT = NULL;
						prevINT = NULL;
			
						break;
					}
				}
			}
		}
	}
	
	for (i = 0; i < FU_FP_SIZE; i++)
	{
		if (fuFP[i] != NULL && fuFP[i]->tom_execute_cycle + FU_FP_LATENCY <= current_cycle)
		{
			insn_struct* currentFP = reservFP;
			insn_struct* prevFP = NULL;

			while (currentFP != NULL)
			{
				if (fuFP[i] == currentFP->insn)
				{
					if (prevFP == NULL)
					{
						/* is the head of list */
						if (WRITES_CDB(currentFP->insn->op))
						{
							commonDataBus = currentFP->insn;
							commonDataBus->tom_cdb_cycle = current_cycle;
						}

						reservFP = currentFP->next;
						currentFP->insn = NULL;
						free(currentFP);
						currentFP = NULL;
						break;
					}
					else
					{
						if (WRITES_CDB(currentFP->insn->op))
						{
							commonDataBus = currentFP->insn;
							commonDataBus->tom_cdb_cycle = current_cycle;
						}

						prevFP->next = currentFP->next;
						currentFP->insn = NULL;
						free(currentFP);
						currentFP = NULL;
						prevFP = NULL;
			
						break;
					}
				}
			}
		}
	}

	/* ECE552 Assignment 4 - END CODE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

	/* ECE552 Assignment 4 - BEGIN CODE */


   insn_struct* tempINT = reservINT;
   insn_struct* tempFP = reservFP;


   if (tempINT != NULL)
   {
     int i;
		 bool is_ready = true;

		 while (tempINT != NULL)
		 {
				if (!tempINT->is_ready)
			  {
					for (i= 0; i < 3; i++) {
					  if (tempINT->insn->Q[i] == NULL) {
					     is_ready &= true; 
					  } else {
				 				is_ready = false;
								break;
					  }
					}

					tempINT->is_ready = is_ready;
				}

			  tempINT = tempINT->next;
		 }
      
   }


   if (tempFP != NULL)
   {
     int i;
		 bool is_ready = true;

		 while (tempFP != NULL)
		 {
				if (!tempFP->is_ready)
				{
					for (i = 0; i < 3; i++) {
					  if (tempFP->insn->Q[i] == NULL) {
					     is_ready &= true; 
					  } else {
				 				is_ready = false;
					  }
					}

					tempFP->is_ready = is_ready;
				}

			  tempFP = tempFP->next;
		 }
      
   }

		tempINT = reservINT;
		tempFP = reservFP;

   while (tempINT != NULL) {
      if (!tempINT->has_fu && tempINT->is_ready && (tempINT->insn->tom_issue_cycle != 0 && tempINT->insn->tom_issue_cycle < current_cycle && tempINT->insn->tom_execute_cycle == 0 )) {
			 if (!set_fu_available(tempINT->insn->op, tempINT->insn)) {
					return;
			 }
		
			 tempINT->insn->tom_execute_cycle = current_cycle;
			 tempINT->has_fu = true;
			 tempINT->is_ready = true;
      }

      tempINT = tempINT->next;
   } 
	
   while (tempFP != NULL) {
      /* if tom_issue_cycle is set(i.e. != 0 has entered issue) than issue cycle of insn should be less than current cycle */
      if (!tempFP->has_fu && tempFP->is_ready && (tempFP->insn->tom_issue_cycle != 0 && tempFP->insn->tom_issue_cycle < current_cycle && tempFP->insn->tom_execute_cycle == 0)) {
			 if (!set_fu_available(tempFP->insn->op, tempFP->insn)) {
					return;
			 }
		
			 tempFP->insn->tom_execute_cycle = current_cycle;
			 tempFP->has_fu = true;
			 tempFP->is_ready = true;
			}
				  
				tempFP = tempFP->next;
   }

   tempINT = NULL;
   tempFP = NULL;

	/* ECE552 Assignment 4 - END CODE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {


	/* ECE552 Assignment 4 - BEGIN CODE */

   instruction_t* head  = instr_queue[0];

   if (head != NULL && head->tom_dispatch_cycle < current_cycle && head->tom_issue_cycle == 0) {
      if (IS_COND_CTRL(head->op) || IS_UNCOND_CTRL(head->op)) {
			 head = NULL;
			 remove_head();
			 /* decrement the instr_queue_size as first instruction is dispatched*/
			 instr_queue_size = instr_queue_size - 1;
      } else if (USES_INT_FU(head->op) || USES_FP_FU(head->op)) {
				 /* check if there is a reservation station available */
				 if (!is_rs_available(head->op)) {	
						return;
				 }

				 insn_struct* temp = set_rs_available(head->op, head);
				 temp->insn->tom_issue_cycle = current_cycle;
				 set_dependent_insn(temp);

				 /* Set the r_out mapping in the maptable */
				 int i;
	
				 for (i =0; i < 2; i++) {
						if (head->r_out[i] != DNA) {
							 map_table[head->r_out[i]] = head;
						}
				 }
						  
				 temp = NULL;
				 head = NULL;
				 remove_head();
				 instr_queue_size = instr_queue_size - 1;
			}
		}

		/* ECE552 Assignment 4 - END CODE */
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace, int current_cycle) {
	
	/* ECE552 Assignment 4 - BEGIN CODE */

  fetch_index++;
  
  while(IS_TRAP(trace->table[fetch_index].op))
  {
  	fetch_index++;
  }
	
  instr_queue[instr_queue_size] = &trace->table[fetch_index];
	instr_queue[instr_queue_size]->tom_dispatch_cycle = current_cycle;
  instr_queue_size++;
	/* ECE552 Assignment 4 - END CODE */
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {
	
	/* ECE552 Assignment 4 - BEGIN CODE */

	if (instr_queue_size < INSTR_QUEUE_SIZE && !fetch_completed) 
  {
		fetch(trace, current_cycle);
	}
	/* ECE552 Assignment 4 - END CODE */
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace) {
   //initialize instruction queue
   int i;
   for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
      instr_queue[i] = NULL;
   }

	/* ECE552 Assignment 4 - BEGIN CODE */

	// removed the initialization for reservation stations as structured has changed.

  /* ECE552 Assignment 4 - END CODE */

		//initialize functional units
		for (i = 0; i < FU_INT_SIZE; i++) {
		  fuINT[i] = NULL;
		}

		for (i = 0; i < FU_FP_SIZE; i++) {
		  fuFP[i] = NULL;
		}

   //initialize map_table to no producers
   int reg;
   for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
      map_table[reg] = NULL;
   }
  
   int cycle = 1;
   while (true) {

			/* ECE552 Assignment 4 - BEGIN CODE */
      
      CDB_To_retire(cycle);
      execute_To_CDB(cycle);
      issue_To_execute(cycle);
      dispatch_To_issue(cycle);
      fetch_To_dispatch(trace, cycle);

	
			if(fetch_index == trace->size - 1)
			{
				if(trace->next == NULL)
				{
					/* fetch has completed */
					fetch_completed = true;
				}
				else
				{
					/* reset the fetch index */
					fetch_index = 0;
					trace = trace->next;
				}
			}

      cycle++;
		/*if (cycle == 19400)
		{
			print_all_instr(trace, 20000);
			/*print_list(reservFP, "reservFP", 2);

			int i;
			for (i = 0; i < INSTR_QUEUE_SIZE; i++)
			{
				if (instr_queue[i] != NULL)
				{
					print_insn(instr_queue[i], "instr_queue");
				}
			}
			if (commonDataBus != NULL)
			print_insn(commonDataBus, "commonDataBus");*/
		//}
			//print_all_instr(trace, 100000);

      if (is_simulation_done(trace, sim_num_insn))
			{
				break;
			}

		/* ECE552 Assignment 4 - END CODE */
   }
  
   return cycle;
}
