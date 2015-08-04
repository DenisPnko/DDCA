/*
 *  ddcaPORT.c
 *  The deterministic DCA
 *  Created by Julie Greensmith on 27/03/2008.
 *	Modified by Feng Gu on 11/07/2008.
 *	The function of calculating MCAV and Kalpha has been integrated.
 *
 *  Modified by Denis Pilipenko on 02/05/2013
 *  Adapted for multiple data stream processing
 *  Dual and Multiple Cooccurrence Analysis integrated
 *  DDCA for the analysis of port scan data
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>
#include <time.h>

#define FACTOR 100
#define NUM_INPUT 2
#define NUM_OUTPUT 3
#define MAX_MIG 10000   /*original migration threshold */
#define NUM_CELL 1001   /*original number of cells in population */
#define TIME_WIN_SAVE 0.001 /*time window for saving timestamps*/
#define TIME_WIN_CO 0.01  /*time window for checking cooccurrence*/


void cooccurrenceRec(int aId);

struct DC
{
    float lifespan;	/*migration threshold countdown */
    float k;	/*K value variable */
    int antigen[99999]; /*local antigen profile */
    int iter; /*the number of iterations of signal updates received*/
    int incarnations;
    int id;
    int totIter;
    int totAg; /*the total amount of antigen a DC has collected per incarnation */
};

struct agtype
{
    float s,m,k,mcav;
    int id;
    int timeNum;    /*timestamp index */
    double t[200];  /*timestamp collection array */
    int antigens[20][2];    /*2D array for storing dual cooccurrences */
    int ant_index;  /*cooccurrence index */
};

/* DC populations initialisation (1-4) */
static struct DC *cell1;
static struct DC *cell2;
static struct DC *cell3;
static struct DC *cell4;

static unsigned int numCells;   /*DC population size */
static float maxMig;    /*migration threshold */

static double timeWinSave;  /* time window for saving timestamps*/
static double timeWinCo;  /* time window for checking the cooccurrence*/

static unsigned int cell_index1;
static unsigned int cell_index2;
static unsigned int cell_index3;
static unsigned int cell_index4;
static unsigned int ags_index;  /*index for dangerous antigen profile */

int cooccurrenceTemp[100][50];   /*array for storing multiple cooccurrences */
int tempIndex1;
int tempIndex2;

char text[20];  /*buffer for user input */

static struct agtype agsG[99999];   /*global antigen profile */

static struct agtype agsD[100];     /*dangerous antigen profile */

/*
 *  dc - the DC structure; numCells - size of the population;
 *  cell - DC population;
 *  A function that initialises a DC in the population
 */
static void initDC(struct DC *dc, int numCells, struct DC *cell)
{
    float tm_interval;
    tm_interval = maxMig / (numCells-1);
    dc->id = dc - cell;
    dc->lifespan = ((dc) - cell) * tm_interval;
    printf("lifespan = %f, tm_interval =%f\n", dc->lifespan, tm_interval);
    dc->iter = 0;
    dc->totIter = 0;
    dc->incarnations = 0;
    dc->totAg = 0;
}

/*
 *  dc - the DC structure;
 *  A function that displays the DC statistics
 */
static void dc_stats(struct DC *dc)
{
    float iterIncarn;
    if(dc->incarnations > 0)
    {
        iterIncarn = (float) dc->totIter / dc->incarnations;
    }
    else
    {
        iterIncarn = dc->totIter;
    }
    printf("DC_id: %d, num incarnations: %d, iter/inc: %f\n", dc->id, dc->incarnations, iterIncarn);
}

/*
 *  str - input; split - separator; toks - array of input elements;
 *  max_toks - maximum number of elements;
 *  A function that parses a single data input
 */
static int easy_explode(char *str, char split, char **toks, int max_toks)
{
    char *tmp;
    int tok;
    int state;

    for(tmp=str,state=tok=0; *tmp && tok < max_toks; tmp++)
    {
        if ( state == 0 )
        {
            if ( *tmp == split )
            {
                toks[tok++] = NULL;
            }
            else if ( !isspace(*tmp) )
            {
                state = 1;
                toks[tok++] = tmp;
            }
        }
        else if ( state == 1 )
        {
            if ( *tmp == split || isspace(*tmp) )
            {
                *tmp = '\0';
                state = 0;
            }
        }
    }

    return tok;
}

/*
 *  ag - antigen id; dc - DC structure; time - timestamp; ags - antigen profile
 *  A function that processes the antigen for a given DC and saves the timestamp
 */
static void do_antigen(pid_t ag, struct DC *dc, double time, struct agtype *ags)
{
    dc->antigen[ag]++;
    if (ags[ag].timeNum >= 0 && ags[ag].timeNum < 200)
    {   // checks that the current timestamp is not within a specified time window
        if(ags[ag].timeNum == 0 || (ags[ag].timeNum > 0 &&
                                    fabs(ags[ag].t[ags[ag].timeNum] - (ags[ag].t[ags[ag].timeNum - 1])) >= timeWinSave))
        {
            ags[ag].t[ags[ag].timeNum] = time;
            ags[ag].timeNum++;
            if (ags[ag].timeNum == 200)
                ags[ag].timeNum = 0;
        }
    }
    if (!ags[ag].timeNum)
    {
        ags[ag].t[0] = time;
        ags[ag].timeNum = 1;
    }
}

/*
 *  dc - DC structure; ags - antigen profile
 *  A function that updates the global antigen profile by a given DC
 */
static void log_antigen(struct DC *dc, struct agtype *ags)
{
    int q;
    int yy;

    for(q =0; q< 99999; q++)
    {
        if(dc->antigen[q])
        {
            dc->totAg +=dc->antigen[q];
            for(yy= 0; yy < dc->antigen[q]; yy++)
            {
                ags[q].k = ags[q].k + dc->k;
                if(dc->k > 0)
                {
                    ags[q].m = ags[q].m + 1;    // update m if mature cell (danger)
                }
                else
                {
                    ags[q].s = ags[q].s + 1;    // update s if semi-mature cell (safe)
                }
            }
            dc->antigen[q] = 0;
        }
    }
    //printf("DC_id: %d, totAg: %d , iter: %d \n", dc->id, dc->totAg, dc->iter);
}

/*
 *  K - K value; csm - CSM value; dc - DC structure; currJ - current cell index; ags - antigen profile;
 *  *cell - DC population;
 *  A function that updates the DC based on the signal's K and CSM values
 */
static void update_DC(float K, float csm, struct DC *dc, int currJ, struct agtype *ags, struct DC *cell)
{
    int tr_interval;
    /* update DC output signals */
    dc->lifespan -= csm;
    dc->k += K;
    dc->iter++;

    if (dc->lifespan <= 0)  // cell reincarnation if lifespan has reached zero
    {
        log_antigen(dc, ags);
        tr_interval = (float) MAX_MIG / (numCells - 1);
        dc->lifespan = ((dc) - cell) * tr_interval;
        dc->k = 0;
        dc->totIter += dc->iter;
        //printf("running totIter %d", dc->totIter);
        //printf("reset DC lifespan is %f \n", dc->lifespan);
        //printf("iterations of cell[%d]: %d \n", currJ, dc->iter);
        dc->iter = 0;
        dc->totAg = 0;
        dc->incarnations++;
    }
    /* pass antigen to the global antigen profile */

}

/*
 *  sig1 and sig2 - danger and safe signals; cell - DC population; num_cells - number of cells;
 *  ags - antigen profile;
 *  A function that processes the incoming signals and passes this information for the DC update
 */
static void do_signals(float sig1, float sig2, struct DC *cell, int num_cells, struct agtype *ags)
{
    float csm;
    float k;
    int j;

    csm = sig1 + sig2;
    k = (sig1 - sig2) - sig2;
    //printf("signal: csm=%f k=%f\n", csm, k);

    for(j=0; j< num_cells; j++)
    {
        update_DC(k, csm, &cell[j], j, ags, cell);
    }

}

/*
 *  *buf - input buffer; *cell - DC population; *cell_index - population's cell index;
 *  *ags - antigen profile;
 *  A function that processes data stream lines and calls the functions for antigen and
 *  signal processing
 */
static void input_line(char *buf, struct DC *cell, int *cell_index, struct agtype *ags)
{
    char *tok[4];
    int n,p;
    int index;
    pid_t ag;
    double time;
    float sig1, sig2;
    char *sp = " "; // this is the separation between attributes
    index = *cell_index;

    n = easy_explode(buf, *sp, tok, 4);

    switch ( n )
    {
    case 3:		/*this is antigen that has 3 fields*/
        if (strcmp(tok[1], "antigen"))
        {
            fprintf(stderr, "wrong antigen input\n");
            getchar();
            exit(EXIT_FAILURE);
        }
        ag = atoi(tok[2]);  // antigen ID
        time = strtod(tok[0], NULL);    // timestamp
        index++;
        index %= numCells;
        do_antigen(ag, &cell[index], time, ags);
        *cell_index = index;

        break;
    case 4:		/*this is for signals that have 4 fields */
        if(strcmp(tok[1], "signal"))
        {
            fprintf(stderr, "wrong signal input\n");
            getchar();
            exit(EXIT_FAILURE);
        }
        sig1 = atof(tok[2]);    // danger signal
        sig2 = atof(tok[3]);    // safe signal

        do_signals(sig1, sig2, cell, numCells, ags);
        break;
    default:
        fprintf(stderr, "wrong input\n");
        getchar();
        exit(EXIT_FAILURE);
    }
}

/*
 * *ags - antigen profile;
 *  A function that calculates the MCAV and K values of the antigens
 *  in the global profile and updates the 'dangerous' antigen profile
 */
static void result(struct agtype *ags)
{
    int i,p;
    float mcav,ka;
    for(i=0; i<99999; i++)
    {
        if((ags[i].m + ags[i].s) != 0)
        {
            mcav = ags[i].m/(ags[i].m + ags[i].s);
            ka = ags[i].k/(ags[i].m + ags[i].s);
            printf("AgType %d %f %f\n", i, mcav, ka);
            if (mcav > 0)
            {
                agsD[ags_index] = ags[i];
                agsD[ags_index].id = i;
                agsD[ags_index].mcav = mcav;
                agsD[ags_index].k = ka;
                agsD[ags_index].ant_index = 0;
                ags_index++;
            }
        }
    }
}

/*
 *  id - antigen ID;
 *  A function that checks if the given antigen has already been
 *  recorded  in any of the cooccurrences
 */
static int checkCooccurrence(int id)
{
    int k,l;
    for(k=0; k<=tempIndex1; k++)
    {
        l = 0;
        while(cooccurrenceTemp[k][l])
        {
            if(id == cooccurrenceTemp[k][l])
                return k;
            l++;
        }
    }
    return -1;
}

/*
 *  id - antigen ID; dId - antigen ID;
 *  A function that returns the ID for the cooccurrence recording
 *  in the antigen's local 2D array
 */
static int checkAntigen(int id, int dId)
{
    int j;
    for(j=0; j< 20; j++)
    {
        if(id == agsD[dId].antigens[j][0])
            return j;
    }
    return -1;
}

/*
 *  Dual Cooccurrence function
 *  A function that compares the timestamps of dangerous antigens and records the matches
 */
static void cooccurrence()
{
    int q,p,i,k,j;
    int aId;
    for(q =0; q < (ags_index-1); q++)
    {
        memset(agsD[q].antigens, 0, sizeof(agsD[q].antigens[0][0]) * 20 * 2);
        for(i = (q+1); i < ags_index; i++)
        {
            for(p=0; p< 200; p++)
            {
                for(k=0; k<200; k++)
                {   // check that the antigens are within the same time window
                    if (agsD[q].t[p] && agsD[i].t[k] && fabs(agsD[q].t[p] - agsD[i].t[k]) <= timeWinCo)
                    {
                        aId = checkAntigen(agsD[i].id, q);
                        if (aId != -1)  // increment the number of matches
                            agsD[q].antigens[aId][1] = agsD[q].antigens[aId][1] + 1;
                        else
                        {   // add a new entry if has not been previously recorded
                            agsD[q].antigens[agsD[q].ant_index][0] = agsD[i].id;
                            agsD[q].antigens[agsD[q].ant_index][1] = agsD[q].antigens[agsD[q].ant_index][1] + 1;
                            agsD[q].ant_index = agsD[q].ant_index + 1;
                        }
                    }
                }
            }
        }
    }
    printf("\nDual Cooccurrence:\n"); // print the Dual cooccurrences
    for(j=0; j<100; j++)
    {
        if(agsD[j].id)
        {
            for (i=0; i<20; i++)
            {
                if (agsD[j].antigens[i][1] != 0)
                    printf("%d - %d (%d times)\n", agsD[j].id, agsD[j].antigens[i][0], agsD[j].antigens[i][1]);
            }
        }
    }
}

/*
 *  Multiple Cooccurrence Function
 *  A function that groups the interconnected antigens into a string
 */
static void multiCooccurrence()
{
    int i,j,l;
    printf("\nMultiple Cooccurrence:\n");
    tempIndex1 = 0;
    for(j=0; j<100; j++)
    {
        if(agsD[j].id)
        {
            tempIndex2 = 0;
            for (i=0; i<20; i++)
            {
                if (agsD[j].antigens[i][1] != 0 && checkCooccurrence(agsD[j].antigens[i][0]) == -1)
                {
                    if (checkCooccurrence(agsD[j].id) == -1)
                    {
                        cooccurrenceTemp[tempIndex1][tempIndex2] = agsD[j].id;
                        tempIndex2++;   // add the first element of the string
                    }
                    cooccurrenceTemp[tempIndex1][tempIndex2] = agsD[j].antigens[i][0];
                    tempIndex2++;   // add the cooccurred elements and increment the index
                    cooccurrenceRec(agsD[j].antigens[i][0]); // start the recursive method with the added antigens
                }
            }
            for (l=0; l<tempIndex2 && tempIndex2 > 2; l++)  // print the results
            {
                printf("%d ", cooccurrenceTemp[tempIndex1][l]);
            }
            if (tempIndex2 > 2)
            {
                printf("\n\n");
                tempIndex1++;
            }
        }
    }
}

/*
 *  A recursive function that supplements the Multiple Cooccurrence function
 */
void cooccurrenceRec(int aId)
{
    int i,j;
    for (i=0; i<100; i++) {
        if (agsD[i].id) {
            for (j=0; j<20; j++)
            {   // check if any other antigens have a cooccurrence with this ID
                if (agsD[i].antigens[j][0] == aId && agsD[i].antigens[j][1] != 0 && checkCooccurrence(agsD[i].id) == -1)
                {
                    cooccurrenceTemp[tempIndex1][tempIndex2] = agsD[i].id;
                    tempIndex2++;
                }
            }
        }
        if (agsD[i].id == aId)
        {
            for (j=0; j<20; j++)
            {   // check if this antigen ID has any other cooccurrences
                if (agsD[i].antigens[j][1] != 0 && checkCooccurrence(agsD[i].antigens[j][0]) == -1)
                {
                    cooccurrenceTemp[tempIndex1][tempIndex2] = agsD[i].antigens[j][0];
                    tempIndex2++;
                    cooccurrenceRec(agsD[i].antigens[j][0]); // apply the same function on new cooccurrences
                }
            }
        }
    }
}

/*
 * A function that saves the results in a file called "output.txt"
 *
 */
void printOutput()
{
    time_t t;
    time(&t);
    int q,j,i,k,l;
    FILE *file;
    file = fopen("output.txt","a+");    // name of the file
    fprintf(file, "\n\n%sAntigen profile:\n", ctime(&t));   // primary Antigen Profile
    for(q =0; q < ags_index; q++)
    {
        fprintf(file, "id %d, mcav %f, k %f\n", agsD[q].id, agsD[q].mcav, agsD[q].k);
    }
    fprintf(file, "\nDual Cooccurrence:\n");  // Dual Cooccurrence Analysis
    for(j=0; j<100; j++)
    {
        if(agsD[j].id)
        {
            for (i=0; i<20; i++)
            {
                if (agsD[j].antigens[i][1] != 0)
                    fprintf(file, "%d - %d (%d times)\n", agsD[j].id, agsD[j].antigens[i][0], agsD[j].antigens[i][1]);
            }
        }
    }
    fprintf(file, "\nMultiple Cooccurrence:\n");  // Multiple Cooccurrence Analysis
    for(k=0; k<=tempIndex1; k++)
    {
        l = 0;
        if (cooccurrenceTemp[k][2])
        {
            while(cooccurrenceTemp[k][l])
            {
                fprintf(file, "%d ", cooccurrenceTemp[k][l]);
                l++;
            }
            fprintf(file, "\n\n");
        }
    }
    fclose(file);
}

/*
 *  A function that takes the input from user
 */
const char * getText()
{
    if ( fgets(text, sizeof text, stdin) != NULL )
    {
        char *newline = strchr(text, '\n');
        if ( newline != NULL )
        {
            *newline = '\0';
        }
    }
    return text;
}

int main(int argc, char **argv)
{
    int numberStr;  // number of Streams
    int verification = -1;
    time_t t;
    time(&t);
    srand(time(NULL));
    printf("Please enter the number of DC (100 - 1001):\n");
    while (verification == -1)
    {
        sscanf(getText(), "%d", &numCells);
        if (numCells >= 100 && numCells <= 1001)
            verification = 1;
        else
            printf("Error: please enter a number from 100 to 1001\n");
    }
    verification = -1;
    printf("Please enter the Migration threshold (1000 - 10001):\n");
    while (verification == -1)
    {
        sscanf(getText(), "%f", &maxMig);
        if (maxMig >= 1000 && maxMig <= 10001)
            verification = 1;
        else
            printf("Error: please enter a number from 1000 to 10001\n");
    }
    verification = -1;
    printf("Please enter the number of streams (1-4):\n");
    while (verification == -1)
    {
        sscanf(getText(), "%d", &numberStr);
        if (numberStr == 1 || numberStr == 2 || numberStr == 3 || numberStr == 4)
            verification = 1;
        else
            printf("Error: please enter a number from 1 to 4\n");
    }

    const char* filename1;
    const char* filename2;
    const char* filename3;
    const char* filename4;
    FILE *file1;
    FILE *file2;
    FILE *file3;
    FILE *file4;
    if (numberStr >= 1)
    {
        printf("Please enter the name of the 1st log:\n");
        filename1 = getText();
        file1 = fopen ( filename1, "r" );
    }
    if (numberStr >= 2)
    {
        printf("Please enter the name of the 2nd log:\n");
        filename2 = getText();
        file2 = fopen ( filename2, "r" );
    }
    if (numberStr >= 3)
    {
        printf("Please enter the name of the 3rd log:\n");
        filename3 = getText();
        file3 = fopen ( filename3, "r" );
    }
    if (numberStr >= 4)
    {
        printf("Please enter the name of the 4th log:\n");
        filename4 = getText();
        file4 = fopen ( filename4, "r" );
    }
    char buf[256];
    int i;
    int p;	/*some counters */
    int q;
    cell_index1 = 0; /* for the selection of DCs per antigen */
    cell_index2 = 0; /* for the selection of DCs per antigen */
    cell_index3 = 0; /* for the selection of DCs per antigen */
    cell_index4 = 0; /* for the selection of DCs per antigen */
    ags_index = 0;
    timeWinSave = (double) TIME_WIN_SAVE;
    timeWinCo = (double) TIME_WIN_CO;
    cell1= calloc(numCells, sizeof(struct DC));
    cell2= calloc(numCells, sizeof(struct DC));
    cell3= calloc(numCells, sizeof(struct DC));
    cell4= calloc(numCells, sizeof(struct DC));

    if(cell1==NULL && cell2==NULL && cell3==NULL && cell4==NULL)
    {
        printf("Error in cell initialisation\n");
        return EXIT_FAILURE;
    }

    // initialise the DCs in the populations
    for(i=0; i < numCells; i++)
    {
        initDC(&cell1[i], numCells, cell1);
        initDC(&cell2[i], numCells, cell2);
        initDC(&cell3[i], numCells, cell3);
        initDC(&cell4[i], numCells, cell4);
    }

    // read the data logs
    if (numberStr >= 1) {
    while (fgets (buf, sizeof(buf), file1) != NULL ) /* read a line */
    {
        char *tmp;
        tmp = strchr(buf, '\n');
        if(tmp)
        {
            *tmp = 0;
        }
        input_line(buf, cell1, &cell_index1, agsG);
    }
    fclose(file1);
    }

    if (numberStr >= 2) {
    while (fgets (buf, sizeof(buf), file2) != NULL ) /* read a line */
    {
        char *tmp;
        tmp = strchr(buf, '\n');
        if(tmp)
        {
            *tmp = 0;
        }
        input_line(buf, cell2, &cell_index2, agsG);
    }
    fclose(file2);
    }

    if (numberStr >= 3) {
    while (fgets (buf, sizeof(buf), file3) != NULL ) /* read a line */
    {
        char *tmp;
        tmp = strchr(buf, '\n');
        if(tmp)
        {
            *tmp = 0;
        }
        input_line(buf, cell3, &cell_index3, agsG);
    }
    fclose(file3);
    }

    if (numberStr >= 4) {
    while (fgets (buf, sizeof(buf), file4) != NULL ) /* read a line */
    {
        char *tmp;
        tmp = strchr(buf, '\n');
        if(tmp)
        {
            *tmp = 0;
        }
        input_line(buf, cell4, &cell_index4, agsG);
    }
    fclose(file4);
    }

    // update the antigens in the global profile
    for(p = 0; p < numCells; p++)
    {
        //printf("flushed cell ID %d\n", p);
        log_antigen(&cell1[p], agsG);
        log_antigen(&cell2[p], agsG);
        log_antigen(&cell3[p], agsG);
        log_antigen(&cell4[p], agsG);
    }

    // print the DC statistics
    for(q =0; q <numCells; q++)
    {
        dc_stats(&cell1[q]);
        dc_stats(&cell2[q]);
        dc_stats(&cell3[q]);
        dc_stats(&cell4[q]);
    }
    free((void*) cell1);
    free((void*) cell2);
    free((void*) cell3);
    free((void*) cell4);

    result(agsG);

    printf("process is finished...\n\n");

    printf("%sAntigen profile:\n", ctime(&t));  // print out the dangerous antigens' profiles
    if(ags_index == 0) {
        printf("No dangerous antigens found\n");
        getchar();
        return EXIT_SUCCESS;
    }
    for(q =0; q < ags_index; q++)
    {
        printf("id %d, mcav %f, k %f\n", agsD[q].id, agsD[q].mcav, agsD[q].k);
    }
    cooccurrence();  // Dual Cooccurrence
    multiCooccurrence(); // Multiple Cooccurrence
    printOutput();  // save the output in a file
    getchar();
    return EXIT_SUCCESS;
}
