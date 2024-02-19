#include<stdio.h>
#include<stdlib.h>
#include<malloc.h>
#define eps 10e-10
void bsort(double* q,int n) //bubble sort
{
   int i,j;
   double temp;
   for( i=0;i<n;i++)
    for(j=n-1;j>i;j--)
    {
        if(q[j]>q[j-1])
        {
           temp=q[j-1];
           q[j-1]=q[j];
           q[j]=temp;
        }
    }
}

double fabs1(double x)
{
    if (x>=0) return x;
    else return -x;
}

int testdom(int *V,double *D, int n,int i,int k,int k1)
//test whether the element is ir-dominated
{
   int p,q;
   for(p=k1;p<k;p++)
    for(q=k+1;q<n;q++)
    {
       if((V[i*n+k]-V[i*n+p])/(D[i*n+k]-D[i*n+p])<=(V[i*n+q]-V[i*n+k])/(D[i*n+q]-D[i*n+k]))
    return 0;
    }
   return 1;
}

int mergesort(int *V,double *D,double *Y,int *L,int *C,int n, int m)
//to choose the element of array which is used to give a lower bound,
//L is the element's line,C is the element's column
{
  int i,j,j1,k,k1=0,k2=0;
  double dtemp;
  int itemp,itemp1;
  for(i=0;i<m;i++)
  {
    k1=k2;
    for(k=0;k<n&&D[i*n+k+1]==0;k++);
     for(j=k;j<n;j++)
     {
       if(testdom(V,D,n,i,j,k)==1)
       {
          L[k2]=i;
          C[k2]=j;
          k2++;
       }
     }
    Y[k1]=1e+10;
    for(j1=k1+1;j1<k2;j1++)
    {
      Y[j1]=(V[L[j1]*n+C[j1]]-V[L[j1-1]*n+C[j1-1]])/(D[L[j1]*n+C[j1]]-D[L[j1-1]*n+C[j1-1]]);
    }
    j=0;
    if(i>0)
    {
      for(j1=k1;j1<k2;j1++)
      {
         for(k=j;k<j1&&Y[k]>Y[j1];k++);
          if(k<j1)
          {
            dtemp=Y[j1];
            itemp=L[j1];
            itemp1=C[j1];
            for(j=j1;j>k;j--)
            {
               Y[j]=Y[j-1];
               L[j]=L[j-1];
               C[j]=C[j-1];
            }
            Y[j]=dtemp;
            L[j]=itemp;
            C[j]=itemp1;
          }
      }
    }
  }
  return k2;
}

void LD(int *V,double *D,double *Y,int *L,int *C,int n, int m,int i,double *UB,double *LB,double c,int length)
//to caculate a lower bound and upper bound
{
   int j=0,j1=0,k=0,itemp=0;
   double y=1e+10;
   double W=0;
   int* l;
   l=(int*)malloc(m*sizeof(int));
   (*LB)=0;
   (*UB)=0;
   if(i>=m)
   {
      free(l);
      return;
   }
   for(j1=0;j1<m-i;j1++)
   {
      (*LB)+=V[L[j1]*n+C[j1]];
      W+=D[L[j1]*n+C[j1]];
      l[L[j1]]=C[j1];
   }
   if(W>c)
   {
      (*UB)=(*LB)+y*(c-W);
      free(l);
      return;
   }
   for(;j1<length;j1++)
   {
      k=l[L[j1]];
      (*LB)=(*LB)+V[L[j1]*n+C[j1]]-V[L[j1]*n+l[L[j1]]];
      W=W+D[L[j1]*n+C[j1]]-D[L[j1]*n+l[L[j1]]];
      l[L[j1]]=C[j1];
      y=Y[j1];
      if(W>c)
      {
        (*LB)=(*LB)-V[L[j1]*n+C[j1]]+V[L[j1]*n+k];
        W=W-D[L[j1]*n+C[j1]]+D[L[j1]*n+k];
        l[L[j1]]=k;
        (*UB)=(*LB)+1+y*(c-W);
        free(l);
        return;
      }
   }
   y=0;
   (*UB)=(*LB)+1+y*(c-W);
   free(l);
   return;
}

int mcknapsack(int *V,double *D,double *Y,int *L,int *C,int n, int m,double c,int length,int *rec1)
//function to compute the solution of MCKP
{
   FILE *in1,*out1;
   int i,k,k1,j,j1,j2,r=0,r1,itemp,length1;
   int nm,nm1;
   int* f;
   double* w;
   int* rec;
   int* itemp1;
   double dtemp=0,dtemp1=0,UB,LB,UB1,LB1;
   double *Y1;
   int* L1;
   int* C1;
   itemp1=(int*)malloc(m*sizeof(int));
   Y1=(double*)malloc(n*m*sizeof(double));
   L1=(int*)malloc(n*m*sizeof(int));
   C1=(int*)malloc(n*m*sizeof(int));
   in1=fopen("error.txt","r");
   out1=fopen("error.txt","w");
   nm=m+1;
   if(n>m+1) nm=n;
   nm1=nm*n*m;
   w=(double*)malloc(nm1*sizeof(double));
//to record the capacity used
   f=(int*)malloc(nm1*sizeof(int));
//to record the value
   rec=(int*)malloc(m*nm1*sizeof(int));
//to record the column of the element chosen in a solution
   length1=0;
   for(k=0;k<length;k++)
   {
      if(L[k]<m)
      {
        Y1[length1]=Y[k];
        L1[length1]=L[k];
        C1[length1]=C[k];
        length1++;
      }
   }
   LD(V,D,Y1,L1,C1,n,m,0,&UB,&LB,c,length1);
//to get an initial lower bound with the capacity of c
   length1=0;
   for(k=0;k<length;k++)
   {
       if(L[k]>0&&L[k]<m)
//to choose all the elements in the array of mergesort
//starting from the second line
       {
          Y1[length1]=Y[k];
          L1[length1]=L[k];
          C1[length1]=C[k];
          length1++;
       }
   }
   for(k=0;k<n&&D[k+1]==0;k++);
//there may be too many zeros in one line, so to skip the ones
//except the last is a good way to save time
   k1=k;
   for(;k<n&&D[k]<=c;k++)
   {
     LD(V,D,Y1,L1,C1,n,m,0,&UB1,&LB1,c-D[k],length1);
//to get a lower bound with all the element choosed from the 2nd
//line to the last line and the capacity is c-D[k]
     if(V[k]+UB1>=LB)
     {
        f[r]=V[k];
        w[r]=D[k];
        rec[r*m]=k;
        r++;
        if(V[k]+LB1>dtemp1) dtemp1=V[k]+LB1;
     }
   }
   if(dtemp1>LB) LB=dtemp1;
//to update lower bound
   w[r]=c;
   f[r]=f[r-1];
   for(i=1;i<m;i++)
   {
     length1=0;
     dtemp1=0;
     for(k=0;k<length;k++)
     {
       if(L[k]>i&&L[k]<m)
       {
          Y1[length1]=Y[k];
          L1[length1]=L[k];
          C1[length1]=C[k];
          length1++;
       }
     }
     for(k1=0;k1<=r;k1++) rec[k1*m+i]=0;
     r1=r;
     for(k=0;k<n&&D[i*n+k+1]==0;k++);
     k1=k;
     for(;k<n;k++)
     {
        for(j=0;j<r;j++)
        {
           if(D[i*n+k]+w[j]<=c)
           {
               for(j1=j;j1<=r&&w[j1]<=D[i*n+k]+w[j];j1++);
               j1--;
               if(f[j1]<f[j]+V[i*n+k])
               {
                 {
                  LD(V,D,Y1,L1,C1,n,m,i+1,&UB1,&LB1,c-D[i*n+k]-w[j],length1);
                  if(f[j]+V[i*n+k]+UB1>=LB)
                  {
                      r1++;
                      if(r1>=nm1)
//to reallocate memory to f,w,rec
//in case the memory allocated at first is not enough
                      {
                        nm1=nm1*2;
                        for(j2=0;j2<r1-1;j2++)
                        {
                          fprintf(out1,"%lf ",w[j2]);
                          if((j2+1)%256==0)
                          fprintf(out1,"\n");
                        }
                        free(w);
                        w=(double*)malloc(nm1*sizeof(double));
                        for(j2=0;j2<r1-1;j2++)
                           fscanf(in1,"%lf ",&w[j2]);
                        for(j2=0;j2<r1-1;j2++)
                        {
                           fprintf(out1,"%d ",f[j2]);
                           if((j2+1)%256==0)
                           fprintf(out1,"\n");
                        }
                        free(f);
                        f=(int*)malloc(nm1*sizeof(int));
                        for(j2=0;j2<r1-1;j2++)
                           fscanf(in1,"%d",&f[j2]);
                        for(j2=0;j2<r1*m-1;j2++)
                        {
                           fprintf(out1,"%d ",rec[j2]);
                           if((j2+1)%256==0)
                           fprintf(out1,"\n");
                        }
                        free(rec);
                        rec=(int*)malloc(m*nm1*sizeof(int));
                        for(j2=0;j2<r1*m-1;j2++)
                        fscanf(in1,"%d",&rec[j2]);
                      }
                      f[r1]=f[j]+V[i*n+k];
                      w[r1]=D[i*n+k]+w[j];
                      for(k1=0;k1<i;k1++) rec[r1*m+k1]=rec[j*m+k1];
                      rec[r1*m+i]=k;
//if a new way of solution is found, saved it at the end of the arrays
                      if(f[j]+V[i*n+k]+LB1>dtemp1) dtemp1=f[j]+V[i*n+k]+LB1;
                  }
                 }
                }
            }
        }
    }
    if(dtemp1>LB) LB=dtemp1;
    if(r1>r)
    {
       for( j1=r+1;j1<=r1;j1++)
       {
          for(j2=0;j2<j1&&w[j2]<w[j1];j2++);
          if(j2<j1)
          {
            itemp=f[j1];
            dtemp=w[j1];
            for(k1=0;k1<m;k1++)
            {
               itemp1[k1]=rec[j1*m+k1];
            }
            for(k=j1;k>j2;k--)
            {
               f[k]=f[k-1];
               w[k]=w[k-1];
               for(k1=0;k1<m;k1++)
               {
                  rec[k*m+k1]=rec[(k-1)*m+k1];
               }
            }
            f[j2]=itemp;
            w[j2]=dtemp;
            for(k1=0;k1<m;k1++)
            {
               rec[j2*m+k1]=itemp1[k1];
            }
          }
//to sort the arrays in the order of w[j],ascending
       }
       r=r1;
       for(j1=0;j1<r;j1++)
       {
          for(j2=j1+1;j2<=r&&f[j2]<=f[j1];j2++)
          {
             f[j2]=f[j1];
             w[j2]=w[j1];
             for(k1=0;k1<m;k1++)
             {
                rec[j2*m+k1]=rec[j1*m+k1];
             }
          }
//if a solution uses more capacity and get less value than the former one,
//use the former,instead
        }
       w[r]=c;
//make sure the last solution record the best solution;
//so let its w use all the capacity
       for(j1=0;j1<r;j1++)
       {
          if(w[j1]==w[j1+1])
          {
             for(j2=j1;j2<r;j2++)
             {
                 w[j2]=w[j2+1];
                 f[j2]=f[j2+1];
                 for(k1=0;k1<m;k1++)
                 {
                     rec[j2*m+k1]=rec[(j2+1)*m+k1];
                 }
             }
             r--;
             j1--;
//to eliminate the solutions that use the same
//capacity but get less value to save memory space
          }
       }
   }
 }
 for(k=0;k<m;k++)
 rec1[k]=rec[r*m+k];
//return the best solution to main function
 itemp=f[r];
 free(rec);
 free(w);
 free(f);
 free(Y1);
 free(L1);
 free(C1);
 return itemp;
}

/*double max(double a,double b)
{
       if(a>b)return(a);
       else return(b);
}*/

int ceil1(double x)
{
    if(x-(int)x>eps)return((int)x+1);
    else return((int)x);
}

void main() 
{
/*Data file should be formated in the following format:
       The size of control group is the first number and the size of treatment 
       group is the second number in the first row of the file. The constraint 
       is the third number at the first row. The fourth number corresponds to
       the percentage to evaluate the up trimmed mean.
       The second row is the control group.
       The third row is the treatment group.
       
  This program is used to find the adjusted treatment observations
  when the trimmed means are controled. The observations in the control group
  will be outputed into the file "control.txt" and the obervations in the 
  treatment group will be outputed into the file "treatment.txt".
*/
   FILE *in,*out,*treatment,*control;
   int n=0,m=0,m1;
   double* x;
   double* y, *ytrimmed;
   double* ny;
   double* s;
   double* Y;
   int* C;
   int* L;
   int* ranky;
   int* nranky;
   double* D;
   int* V;
   double c=0,alpha;
   int i,j,j1;
   int length;
   int* r;
   int count;
   char protect;
   if((in=fopen("data.txt","r"))==NULL)
   {
      printf("Cannot open the file!\n");
      printf("\nQuit?(Y/N)");
      protect=toupper(getchar());
      while(protect!='Y')
      { printf("\nQuit?(Y/N)");
        protect=toupper(getchar());
      };
      exit(0);
   }
   out=fopen("result.txt","w+");
   treatment=fopen("treatment.txt","w+");
   control=fopen("control.txt","w+");
   fscanf(in,"%d %d %lf %lf",&n,&m,&c,&alpha);
   if(c<0){
      printf("The constraint must be non-negative!\n");
      exit(0);
   }
   if(alpha<0 || alpha>=1){
      printf("The trimmed percentage must be within [0,1)!\n");
      exit(0);
   }
// input the length of array x,y, and the capacity
   x=(double*)malloc(n*sizeof(double));
   for(i=0;i<n;i++)
     fscanf(in,"%lf",&x[i]);//input the element of array x
   m1=m;
   m=m-ceil1(m*alpha);
   c=m*c;
   y=(double*)malloc(m*sizeof(double));
   ytrimmed=(double*)malloc(m1*sizeof(double));
   ny=(double*)malloc(m*sizeof(double));
   s=(double*)malloc((n+m)*sizeof(double));
   r=(int*)malloc(m*sizeof(int));
   ranky=(int*)malloc(m*sizeof(int));
   nranky=(int*)malloc(m*sizeof(int));
   Y=(double*)malloc((n+1)*m*sizeof(double));
   L=(int*)malloc((n+1)*m*sizeof(double));
   C=(int*)malloc((n+1)*m*sizeof(double));
   for(i=0;i<m1;i++)
     fscanf(in,"%lf",&ytrimmed[i]);
//input the element of array y
   D=(double*)malloc((n+1)*m*sizeof(double));
   V=(int*)malloc((n+1)*m*sizeof(int));
   bsort(x,n);
   bsort(ytrimmed,m1);
//sort x and y array first,descending
   for(i=0;i<m1;i++)
   {
       if(i<m1-m){ytrimmed[i]=x[n-1];}
       else{y[i-(m1-m)]=ytrimmed[i];}
   }
   
   for(i=m-1;i>=0;i--)
   {
      for(j=n-1;j>=0&&x[j]<y[i];j--);
         ranky[i]=n-j+m-1-i;
   }
   alpha=y[0];
   for(i=0;i<m;i++)
//caculate matrix D and V,if x[j]>=y[i], D[i][j]=0,V[i][j]=0,
//if x[j]<y[i],D[i][j]=y[j]-x[i],V[i][j]++
   {
     j1=0;
     D[i*(n+1)]=0;
     V[i*(n+1)]=0;
     for(j=0;j<n;j++)
     {
         if(y[i]-x[j]>0)
         {
            j1++;
            D[i*(n+1)+j+1]=y[i]-x[j];
            V[i*(n+1)+j+1]=j1;
            if(alpha>D[i*(n+1)+j+1])alpha=D[i*(n+1)+j+1];
         }
         else
         {
            D[i*(n+1)+j+1]=0;
            V[i*(n+1)+j+1]=0;
         }
     }
   }
//if you need to read D and V matrix, use the code below
/* for(i=0;i<m;i++) //output D
{
for(j=0;j<n+1;j++)
{
fprintf(out,"%lf",D[i*(n+1)+j]);
fprintf(out," ");
}
fprintf(out," \n");
}
fprintf(out," \n");
for(i=0;i<m;i++) //output V
{
for(j=0;j<n+1;j++)
{
fprintf(out,"%d",V[i*(n+1)+j]);
fprintf(out," ");
}
fprintf(out," \n");
}
fprintf(out," \n");*/
 if(alpha<c){
   length=mergesort(V,D,Y,L,C,n+1,m);
   count=mcknapsack(V,D,Y,L,C,n+1,m,c,length,r);
   j1=0;
   for(i=0;i<m;i++)
   {
      c-=D[i*(n+1)+r[i]];
//to get the left capacity
   }
   for(i=0;i<m;i++)
   {
      ny[i]=y[i]-D[i*(n+1)+r[i]];
      nranky[i]=1;
   }
   for(i=0;i<n;i++)
      s[i]=x[i];
   for(i=n;i<n+m;i++)
      s[i]=ny[i-n];
      bsort(s,n+m);
   for(i=0;i<m;i++)
   {
      for(j=n+m-1;j>=0;j--)
      {
        if(fabs1(s[j]-ny[i])<eps)
        {
           nranky[i]=n+m-j;
           for(j1=0;j1<i;j1++)
           {
               if(fabs1(s[j]-ny[j1])<eps) nranky[i]++;
           }
           j=-1;
        }
      }
    }
//the code above is to get the new rank of each y[i]
    for( i=0;i<m;i++){
    //   fprintf(out,"%lf original rank: %d final rank: %d reduced value: %lf\n",y[i],ranky[i],nranky[i],D[i*(n+1)+r[i]]);
       //fprintf(treatment,"%lf\n",y[i]-D[i*(n+1)+r[i]]-eps*(i+1));
       ytrimmed[i+m1-m]=y[i]-D[i*(n+1)+r[i]];
    }
  }
  bsort(ytrimmed,m1);
  for(i=0;i<m1;i++)
  {
        fprintf(treatment,"%lf\n",ytrimmed[i]);
  }
  //fprintf(out,"Reduced sum of ranks %d\n", count);
  fprintf(out,"Budget left: %lf\n",c);
  for(i=0;i<n;i++){
       fprintf(control,"%lf\n",x[i]);
  }
  free(x);
  free(y);
  free(ny);
  free(ranky);
  free(nranky);
  free(s);
  free(D);
  free(V);
  /*printf("\nQuit?(Y/N)");
  protect=toupper(getchar());
  while(protect!='Y')
  { printf("\nQuit?(Y/N)");
        protect=toupper(getchar());
  };*/
}
