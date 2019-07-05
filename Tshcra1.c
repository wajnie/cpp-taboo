/* wersja dla Cmax i roznych alfa (1 lub 2) z heurystyczna procedura
   przudzialu zasobu ciaglego - funkcja heuristic_makespan
   statyczne tablice
   oraz parametry z linii polecen, brak mierzenia czasu,
   TS z oryginalnym sasiedztwem i metoda TNM,
   funkcja makespan wywoluje solver nieliniowy,
   m-tki i pozycje w m-tkach numerowane od 0, takze tablice beg_ i end_table,
   wszystko dotyczace zadan numerowane od 1 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <values.h>
#include "cfsqpusr.h"

typedef unsigned   int word;

const word    maxalfa=2;          /* maksymalny wspolczynnik alfa */
const word    maxx=100;           /* maksymalny stan koncowy zadania */
const word    maxn=25;            /* maksymalna liczba zadan */
const word    maxm=5;             /* maksymalna liczba maszyn */
const word    list_length=7;      /* maksymalna liczba elementow na liscie */
const word    maxsol=1000;        /* maksymalna liczba rozwiazan */

typedef word       vector[maxn];  /* tablica n liczb naturalnych */
typedef word       matrix[maxn][maxm]; /* tablica dwuwymiarowa liczb naturalnych */
typedef matrix     solution;      /* sekwencja dopuszczalna */
typedef word       tuple2[2];     /* dwojka liczb naturalnych */
typedef tuple2     range;         /* zakres wystepowania zadan */
typedef word       tuple3[3];     /* trojka liczb naturalnych */
typedef tuple3     move;          /* przejscie */
typedef tuple2     r_move;        /* przejscie odwrotne - komb. i zadanie */
struct  list_elem   { list_elem *prev; move elem1;
                      double elem2; list_elem *next; };
                                  /* element listy: przejscie odwrotne,
                                  najlepsza wartosc dotad i wskazniki */
typedef list_elem   *list_pointer;
enum    boolean    { FAL=0, TRU=1 };

solution      bestsol,         /* najlepsze znalezione dotad rozwiazanie */
              currsol,         /* rozwiazanie biezace */
              solvsol;         /* rozwiazanie dla solwera */
list_pointer  beg_list,
              end_list;        /* wskazniki na poczatek i koniec listy */
word          list_card,       /* aktualna licznosc listy */
              finst,           /* numer pierwszej instancji */
              linst,           /* numer ostatniej instancji */
              nbinst,          /* numer biezacej instancji */
              nbiter,          /* numer biezacej iteracji */
              bestiter,        /* numer iteracji z najlepszym rozwiazaniem */
              nbsol,           /* liczba dotad sprawdzonych rozwiazan */
              nbbestsol,       /* numer najlepszego dotad rozwiazania */
              hmr,             /* liczba restartow */
              n,m;             /* liczba zadan i maszyn */
vector        x_table,         /* tablica stanow koncowych zadan */
              alfa,            /* tablica wspolczynnikow alfa zadan */
              beg_table,       /* tablica zadan rozpoczynajacych sie w
                                  kombinacjach od drugiej do ostatniej */
              end_table,       /* tablica zadan konczacych sie w kombinacjach
                                  od pierwszej do przedostatniej */
              end_table_n;     /* tablica end_table dla kolejnych sasiadow */
range         job_range[maxn]; /* tablica dwojek oznaczajacych poczatkowa
                                  i koncowa kombinacje zadania */
move          tl;              /* lista jednoelementowa TL - zawiera przejscie
                                  bezposrednio odwrotne do ostatniego */
double 	      m_bestsol,       /* funkcja celu najlepszego rozwiazania */
              m_currsol,       /* funkcja celu biezacego rozwiazania */
              m_exact;         /* funkcja celu obliczona przez solver */
FILE          *resfile1,       /* plik z wynikami */
              *resfile2;       /* plik z informacjami */
char          *filename1 [15], /* nazwa pliku z wynikami */
              *filename2 [15]; /* nazwa pliku z informacjami */

word generator (word range) {
   return rand() % range; }

void disp_sol (solution s) {
word i,j;
   for (i=0; i<n-m+1; i++) {
      printf("(");
      for (j=0; j<m; j++) {
         printf("%u ",s[i][j]);
         if (j==m-1)
            printf(")"); } }
   printf("\n"); }

void write_sol (solution s) {
word i,j;
   for (i=0; i<n-m+1; i++) {
      fprintf(resfile2,"(");
      for (j=0; j<m; j++) {
         fprintf(resfile2,"%u ",s[i][j]);
         if (j==m-1)
            fprintf(resfile2,")"); } } }

void copy_sol (solution s1, solution s2) {
word i,j;
   for (i=0; i<n-m+1; i++)
   for (j=0; j<m; j++)
      s2[i][j]=s1[i][j]; }

void copy_move (move e1, move e2) {
word i;
   for (i=0; i<3; i++)
      e2[i]=e1[i]; }

void reverse_move (move e1, move e2) {
   e2[0]=e1[0];
   e2[1]=e1[2];
   e2[2]=e1[1]; }

boolean comp_moves (move e1, move e2) {
boolean equal;
word i;
   equal=TRU;
   i=0;
   while (equal && i<3) {
      equal=(boolean)(equal && e1[i]==e2[i]);
      i++; }
   return equal; }

void shorten_move (move e1, r_move e2) {
   e2[0]=e1[0];
   e2[1]=e1[2]; }

void copy_r_move (r_move e1, r_move e2) {
   e2[0]=e1[0];
   e2[1]=e1[1]; }

boolean comp_r_moves (r_move e1, r_move e2) {
   if (e1[0]!=e2[0])
      return FAL;
   else
      if (e1[1]==e2[1])
         return TRU;
      else
         return FAL; }

void clean_list (void) {
list_pointer p,q;
   p=beg_list;
   while (p!=NULL) {
      q=(*p).next;
      delete p;
      p=q; }
   beg_list=end_list=NULL;
   list_card=0; }

list_pointer where_on_list (r_move e) {
list_pointer p;
boolean is;
   is=FAL;
   p=beg_list;
   while (p!=NULL && !is) {
      is=comp_r_moves((*p).elem1,e);
      if (!is)
         p=(*p).next; }
   return p; }

void append (r_move e, double m_e) {
list_pointer p;
   p=end_list;
   end_list=new list_elem;
   copy_r_move(e,(*end_list).elem1);
   (*end_list).elem2=m_e;
   (*end_list).prev=p;
   (*end_list).next=NULL;
   if (p!=NULL)
      (*p).next=end_list;
   else
      beg_list=end_list;
   list_card++; }

void remove (void) {
list_pointer p;
   p=(*beg_list).next;
   (*p).prev=NULL;
   delete beg_list;
   beg_list=p;
   list_card--; }

void modify_list (move e, double m_e, list_pointer p) {
move erev;
r_move erevsh;
   reverse_move(e,erev);
   shorten_move(erev,erevsh);
   if (p==NULL) {
      append(erevsh,m_e);
      if (list_card>list_length)
         remove(); }
   else {
      copy_r_move(erevsh,(*p).elem1);
      (*p).elem2=m_e; }
   copy_move(erev,tl); }

void tabu (move e, double m_e, boolean &aspir, list_pointer &p) {
r_move esh;
   shorten_move(e,esh);
   p=where_on_list(esh);
   if (p==NULL)
      aspir=TRU;
   else
      if ((*p).elem2 > m_e)
         aspir=TRU;
      else
         aspir=FAL; }

void modify_tables (move e) {
   if (e[0]==job_range[e[1]][0]) {
      job_range[e[1]][0]++;
      job_range[e[2]][0]--;
      if (e[0]!=0) {
         beg_table[e[0]-1]=e[2];
         beg_table[e[0]]=e[1]; }
      else
         beg_table[e[0]]=e[1]; }
   else {
      job_range[e[1]][1]--;
      job_range[e[2]][1]++;
      if (e[0]!=n-m) {
         end_table[e[0]]=e[2];
         end_table[e[0]-1]=e[1]; }
      else
         end_table[e[0]-1]=e[1]; } }

void construct_etn (move e) {
word k;
   for (k=0; k<n-m; k++)
      end_table_n[k]=end_table[k];
   if (e[0]==job_range[e[1]][1])
      if (e[0]!=n-m) {
         end_table_n[e[0]]=e[2];
         end_table_n[e[0]-1]=e[1]; }
      else
         end_table_n[e[0]-1]=e[1]; }

word domain (solution s, word k, word l) {
word mbeg,mend;
   mbeg=job_range[s[k][l]][0];
   mend=job_range[s[k][l]][1];
   if ((mbeg==mend) || (k>mbeg && k<mend))
      return 0;
   else {
      if (k==0)
         return beg_table[k];
      else
         if (k==n-m)
            return end_table[k-1];
         else {
            if (k==mbeg)
               return beg_table[k];
            else
               return end_table[k-1]; } } }

void obj32 (int nparam, int j, double* x, double* fj, void* cd) {
int i,k;
double b,c_2;
   *fj=0.0;
   for (i=0; i<n-m+1; i++) {
      b=c_2=0.0;
      for (k=0; k<m; k++)
        if (alfa[solvsol[i][k]]==1)
           b+=x[i*m+k];
        else
           c_2+=x[i*m+k]*x[i*m+k];
      *fj+=b+sqrt(b*b+4*c_2); }
   *fj=*fj/2.0; }

void cntr32 (int nparam, int j, double* x, double* gj, void *cd) {
int i,k;
   *gj=x_table[j];
   for (i=0; i<n-m+1; i++)
   for (k=0; k<m; k++)
      if (solvsol[i][k]==j)
         *gj-=x[i*m+k]; }

double solver (void) {
   int nparam,nf,nineq,neq,mode,iprint,miter,neqn,nineqn,
       ncsrl,ncsrn,nfsr,mesh_pts[1],inform,i,k;
   double bigbnd,eps,epsneq,udelta,result;
   double *x,*bl,*bu,*f,*g,*lambda;
   void *cd;

                        /* wybor algorytmu ! */
   mode=100;
                        /* opcje wyprowadzania wynikow */
   iprint=0;
                        /* maksymalna dopuszczalna liczba iteracji */
   miter=5000;
                        /* pelni role nieskonczonosci */
   bigbnd=1.e10;
                   /* jakas norma - musi byc wieksza od precyzji maszyny */
   eps=1.e-3;
             /* maksymalne naruszenie ograniczen rownosciowych nieliniowych */
   epsneq=1.e-1;
                        /* rozmiar perturbacji (?)- najlepiej zeby bylo 0.0 */
   udelta=0.e0;
                        /* liczba zmiennych swobodnych */
   nparam=(n-m+1)*m;
                        /* liczba funkcji celu */
   nf=1;
                        /* liczba ograniczen rownosciowych nieliniowych */
   neqn=0;
                        /* liczba ograniczen nierownosciowych nieliniowych */
   nineqn=0;
                        /* calkowita liczba ograniczen nierownosciowych */
   nineq=0;
                        /* calkowita liczba ograniczen rownosciowych */
   neq=n;
                        /* dotyczy ograniczen zwiazanych (?)*/
   ncsrl=ncsrn=nfsr=mesh_pts[0]=0;
                        /* tablica dolnych ograniczen */
   bl=(double*)calloc(nparam,sizeof(double));
                        /* tablica gornych ograniczen */
   bu=(double*)calloc(nparam,sizeof(double));
                        /* tablica zmiennych swobodnych */
   x=(double*)calloc(nparam,sizeof(double));
                        /* tablica wartosci funkcji celu */
   f=(double*)calloc(nf+1,sizeof(double));
                        /* tablica ograniczen */
   g=(double*)calloc(nineq+neq+1,sizeof(double));
   lambda=(double*)calloc(nineq+neq+nf+nparam,sizeof(double));

/* ustalenie dolnych bl, gornych bu ograniczen i rozwiazan startowych x */
   for (i=0; i<(n-m+1)*m; i++) {
      bl[i]=0.0;
      bu[i]=double(n*maxx);
      x[i]=0.0; }

   for (i=0; i<n; i++) {
      for (k=0; solvsol[k/m][k%m]!=(i+1); k++);
      x[k]=x_table[i+1]; }

   cfsqp(nparam,nf,nfsr,nineqn,nineq,neqn,neq,ncsrl,ncsrn,mesh_pts,
         mode,iprint,miter,&inform,bigbnd,eps,epsneq,udelta,bl,bu,x,f,g,
         lambda,obj32,cntr32,grobfd,grcnfd,cd);

   free(bl);
   free(bu);
   free(x);
   result=f[0];
   free(f);
   free(g);
   free(lambda);
   return result; }

double makespan (solution s) {
   copy_sol(s,solvsol);
   return solver(); }
//   return (double)generator(500); }

void on_machines (solution s, solution sm) {
word z,i,j,k;
boolean is;
   copy_sol(s,sm);
   for (i=0; i<n-m; i++)
   for (j=0; j<m; j++) {
      is=FAL;
      k=0;
      while (k<m && !is)
         if (sm[i][j]==sm[i+1][k])
            is=TRU;
         else
            k++;
      if (is)
         if (k!=j) {
            z=sm[i+1][j];
            sm[i+1][j]=sm[i+1][k];
            sm[i+1][k]=z; } } }

double heuristic_makespan (solution s) {
double mload[maxm],
       maps[maxm],
       u_k[maxm],
       c_k[maxn-maxm],
       x_rest[maxn],
       sum,sum1,sum2,total_load,clb,u,c_max;
word i,j,k,l;
   on_machines(s,solvsol);
   nbsol++;
   for (i=1; i<n+1; i++)
      x_rest[i]=(double)x_table[i];
   for (k=0; k<n-m; k++) {
      for (j=0; j<m; j++) {
         sum=0.0;
         l=0;
         while (l<n-m+1) {
            if (alfa[solvsol[l][j]]==1)
               sum+=x_rest[solvsol[l][j]]*m;
            else
               sum+=x_rest[solvsol[l][j]]*sqrt(m);
            while (solvsol[l+1][j]==solvsol[l][j] && l<n-m)
               l++;
            if (l<n-m+1)
               l++; }
         mload[j]=sum; }
      total_load=0.0;
      for (j=0; j<m; j++)
         total_load+=mload[j];
      clb=total_load/m;
      for (j=0; j<m; j++)
         maps[j]=mload[j]/clb;
      u=0.0;
      for (j=0; j<m; j++) {
         if (alfa[solvsol[k][j]]==1)
            u_k[j]=maps[j];
         else
            u_k[j]=pow(maps[j],2.0);
         u+=u_k[j]; }
      for (j=0; j<m; j++)
         u_k[j]/=u;
      for (j=0; solvsol[k][j]!=end_table_n[k]; j++);
      if (alfa[end_table_n[k]]==1)
         c_k[k]=x_rest[end_table_n[k]]/u_k[j];
      else
         c_k[k]=x_rest[end_table_n[k]]/sqrt(u_k[j]);
      for (j=0; j<m; j++) {
         if (alfa[solvsol[k][j]]==1)
            x_rest[solvsol[k][j]]-=c_k[k]*u_k[j];
         else
            x_rest[solvsol[k][j]]-=c_k[k]*sqrt(u_k[j]);
         if (x_rest[solvsol[k][j]] < 0.0)
            x_rest[solvsol[k][j]]=0.0; } }
   k=n-m;
   sum1=sum2=0.0;
   for (j=0; j<m; j++)
      if (alfa[solvsol[k][j]]==1)
         sum1+=x_rest[solvsol[k][j]];
      else
         sum2+=pow(x_rest[solvsol[k][j]],2.0);
   sum=(sum1+sqrt(pow(sum1,2.0)+4*sum2))/2.0;
   c_max=0.0;
   for (k=0; k<n-m; k++)
      c_max+=c_k[k];
   c_max+=sum;
   return c_max; }

word find_max (vector t) {
word max,ind,i;
   ind=1;
   max=t[1];
   for (i=2; i<n+1; i++)
      if (t[i]>max) {
         max=t[i];
         ind=i; }
   t[ind]=0;
   return ind; }

void rand_sol (solution s) {
boolean global_fit[maxn],local_fit[maxn];
word place,i,j;
   for (i=1; i<n+1; i++)
      global_fit[i]=local_fit[i]=TRU;
   for (i=0; i<m; i++) {
      do
	 s[0][i]=generator(n)+1;
      while (!local_fit[s[0][i]]);
      job_range[s[0][i]][0]=0;
      local_fit[s[0][i]]=FAL; }
   for (i=1; i<n-m+1; i++) {
      for (j=1; j<n+1; j++)
         local_fit[j]=TRU;
      for (j=0; j<m; j++) {
         s[i][j]=s[i-1][j];
         local_fit[s[i-1][j]]=FAL; }
      place=generator(m);
      end_table[i-1]=s[i-1][place];
      job_range[s[i-1][place]][1]=i-1;
      global_fit[s[i-1][place]]=FAL;
      do
         s[i][place]=generator(n)+1;
         while (!global_fit[s[i][place]] || !local_fit[s[i][place]]);
      beg_table[i-1]=s[i][place];
      job_range[s[i][place]][0]=i; }
   for (i=0; i<=m-1; i++)
      job_range[s[n-m][i]][1]=n-m;
   for (i=0; i<n-m; i++)
      end_table_n[i]=end_table[i]; }

void set_start_sol (solution s) {
vector app_table,x_copy,relations;
range range_copy[maxn];
word i,j;
   rand_sol(s);
   for (i=1; i<n+1; i++)
      app_table[i]=0;
   for (i=0; i<n-m+1; i++)
   for (j=0; j<m; j++)
      app_table[s[i][j]]++;
   for (i=1; i<n+1; i++)
      x_copy[i]=x_table[i];
   for (i=1; i<n+1; i++)
      relations[find_max(app_table)]=find_max(x_copy);
   for (i=0; i<n-m+1; i++)
   for (j=0; j<m; j++)
      s[i][j]=relations[s[i][j]];
   for (i=0; i<n-m; i++) {
      beg_table[i]=relations[beg_table[i]];
      end_table[i]=relations[end_table[i]]; }
   for (i=1; i<n+1; i++) {
      range_copy[relations[i]][0]=job_range[i][0];
      range_copy[relations[i]][1]=job_range[i][1]; }
   for (i=1; i<n+1; i++) {
      job_range[i][0]=range_copy[i][0];
      job_range[i][1]=range_copy[i][1]; }
   for (i=0; i<n-m; i++)
      end_table_n[i]=end_table[i]; }

void restart (solution s, double &m_s) {
   rand_sol(s);
   m_s=heuristic_makespan(s);
   if (m_s < m_bestsol) {
      copy_sol(s,bestsol);
      m_bestsol=m_s;
      bestiter=nbiter;
      nbbestsol=nbsol; }
   clean_list();
   tl[0]=tl[1]=tl[2]=0;
   hmr++; }

void iteration (solution s, double &m_s) {
solution neigh,bestneigh;
move mv,bestmove;
list_pointer where,bestwhere;
const double very_big_num=MAXDOUBLE;
double m_bestneigh,m_neigh;
boolean aspiration;
word z,i,j;
   m_bestneigh=very_big_num;
   i=j=0;
   while (i<n-m+1) {
      z=domain(s,i,j);
      if (z!=0) {
         mv[0]=i;
         mv[1]=s[i][j];
         mv[2]=z;
         if (!comp_moves(mv,tl)) {
            copy_sol(s,neigh);
            neigh[i][j]=z;
            construct_etn(mv);
            m_neigh=heuristic_makespan(neigh);
            tabu(mv,m_neigh,aspiration,where);
            if (aspiration)
               if (m_neigh < m_bestneigh) {
                  copy_sol(neigh,bestneigh);
                  m_bestneigh=m_neigh;
                  copy_move(mv,bestmove);
                  bestwhere=where; } } }
      j++;
      if (j>=m) {
         j=0;
         i++; } }
   if (m_bestneigh < very_big_num) {
      if (m_bestneigh < m_bestsol) {
         copy_sol(bestneigh,bestsol);
         m_bestsol=m_bestneigh;
         bestiter=nbiter;
         nbbestsol=nbsol; }
      copy_sol(bestneigh,s);
      m_s=m_bestneigh;
      modify_list(bestmove,m_bestneigh,bestwhere);
      modify_tables(bestmove); }
   else
      restart(s,m_s) ; }

void parameters (int hmpar, char *par[]) {
word k;
   k=1;
   n=(word)atoi(par[k]);
   k++;
   m=(word)atoi(par[k]);
   k++;
   (*filename1)=par[k];
   k++;
   (*filename2)=par[k];
   k++;
   finst=(word)atoi(par[k]);
   k++;
   linst=(word)atoi(par[k]); }

void initiation (void) {
word i;
   clean_list();
   tl[0]=tl[1]=tl[2]=0;
   nbiter=bestiter=nbsol=nbbestsol=hmr=0;
   srand(nbinst);
   for (i=1; i<n+1; i++) {
      x_table[i]=generator(maxx)+1;
      alfa[i]=generator(maxalfa)+1; }
   set_start_sol(currsol);
   m_currsol=heuristic_makespan(currsol);
//   m_exact=makespan(currsol);
//   disp_sol(currsol);
//   printf("%f %f\n",m_currsol,m_exact);
   copy_sol(currsol,bestsol);
   m_bestsol=m_currsol; }

void results (void) {
   m_exact=makespan(bestsol);
   resfile1=fopen(*filename1,"at");
   resfile2=fopen(*filename2,"at");
   fprintf(resfile1,"%3u) %4.3f %4.3f\n",nbinst,m_bestsol,m_exact);
   fprintf(resfile2,"%3u) ",nbinst);
   write_sol(bestsol);
   fprintf(resfile2," %3u %3u %3u %3u %3u \n",nbbestsol,nbsol,
      bestiter,nbiter,hmr);
   fclose(resfile1);
   fclose(resfile2); }

void conclusion (void) {
   clean_list(); }

main(int hmpar, char *par[]) {
   parameters(hmpar,par);
   for (nbinst=finst; nbinst<=linst; nbinst++) {
       initiation();
       while (nbsol<=maxsol) {
          nbiter++;
          iteration(currsol,m_currsol); }
//          m_exact=makespan(currsol);
//          disp_sol(currsol);
//          printf("%u %f %f %u\n",nbiter,m_currsol,m_exact,bestiter); }
       results(); }
   conclusion(); }
