/* Monte Calo Simulation with chain energy
 for M chains(length N) in D*D*D cube */
/*将完美晶体熔化，变成我们需要的带一个模板的初始态1111111*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#define DX 64
#define DY 64
#define DZ 64
#define M 1
#define N 128
#define F1 "chushitai128.ord"
#define F2 "Gyrational_radius.dat"

//#define E 1 /*this is the Ec/Ep value */
#define TempNUM 0 //the chain number of tempelate
#define R 0 /*this is the Er/Ep value */
#define Output 100
#define repeatuplimit 10000
//int output2 = 1;

int direction=1;
double F=0.00;

int T = 100;
int k;
int repeat = 0;
int periodcycle = 0;
int cx, cy, cz;
int bjY(int x), abjY(int x, int y), tfY(int x);
int bjX(int x), abjX(int x, int y), tfX(int x);
int bjZ(int x), abjZ(int x, int y), tfZ(int x);
int fp(int a, int b, int i);
int je(int x1, int y1, int z1, int x2, int y2, int z2), jc(int c, int i);
int hindbend(int a, int b, int c, int x, int y, int z, int l);
double dist(int x, int y, int z)/*,calc(void)*/;
int jpv(int x, int y, int z, int s);
double ran(long t);
int xx[M + 1][N + 2];
int yy[M + 1][N + 2];
int zz[M + 1][N + 2];
int ii[DX + 1][DY + 1][DZ + 1];
int jj[DX + 1][DY + 1][DZ + 1];
int xemax[8 + 1], xfmax[8 + 1];
int xx0[M + 1][N + 2];
int yy0[M + 1][N + 2];
int zz0[M + 1][N + 2];
double density[N + 1][N + 1];
double displace[10000][100 + 1];
int max(int	x,int	y,int	z);


/*****
 * The main function.
 *****/
main(void)
{
	FILE * infile; /* Input file. */
	char filename[50]; /* Input line buffer */
	int a,b,c,d,xc,yc,zc,i1,nn=1,cycle=0,L,r,cn,n,s=0,v=0,nv;
	int i,j,j1,j2,j3,j4,x,y,z,p;
	int num=1,x1,y1,z1,x2,y2,z2; /* the run number */
	double l,l1,l2,lb=0.0,le=0.0,lc=0.0,temp=T/100.0; /*the distance between neibouring beads */
	int centx,centy,centz,centx1,centy1,centz1;
	double gyration_x,gyration_y,gyration_z,gyration_sum,gyration_x_sum,gyration_y_sum,gyration_z_sum,monomerdensity_sample_num;
	int gyration_sample_num;
	float interval=0.001;
	time_t t;
	int maxj,minj;//求得距离质心最远的两点编号
	int countt[N+1];//记录最远端编号出现数目

	for(i=1;i<=N;i++)
        countt[i]=0;

	/* input the initial state*/
	infile=fopen(F2,"w");
	fprintf(infile,"Cycle\tF\tGyration_x\tGyration_y\tGyration_z\tGyration radius\n");
	fclose(infile);

	for (x=1;x<=DX;x++)
	for (y=1;y<=DY;y++)
	for (z=1;z<=DZ;z++)
	ii[x][y][z]=0,jj[x][y][z]=-1;

	gyration_sum=gyration_x_sum=gyration_y_sum=gyration_z_sum=0.0;
    gyration_sample_num=0;
	l=ran(-time(&t));

	infile = fopen(F1, "r" );
	if ( !infile )
	{
		printf( "Can't open input file!\n" );
		exit(1);}
	for (i=1;i<=M;i++)
	for (j=1;j<=N;j++)
	{
		fscanf(infile,"%i	%i	%i\n",&a,&b,&c);
		xx[i][j]=xx0[i][j]=a;
		yy[i][j]=yy0[i][j]=b;
		zz[i][j]=zz0[i][j]=c;
		a=tfX(a),b=tfY(b),c=tfZ(c);
		ii[a][b][c]=i;
		jj[a][b][c]=j;
	}
	fclose(infile);

	for(i=1;i<=10000;i++)
	for(a=0;a<=100;a++)
	displace[i][a]=0.00;
	centx=centy=centz=0;


	/* go through every vacancy once */
	start:
	for (k=1;k<=M*N;k++)
	{
		i=(int)(ran(1000000)*M)+1;
		if(i<=TempNUM)continue;
		j=(int)(ran(1000000)*N)+1;//随机出链中第j个链单元进行模拟
		x=xx[i][j];
		y=yy[i][j];
		z=zz[i][j];
		x=tfX(x);
		y=tfY(y);
		z=tfZ(z);
        //随机取出一个链单元
		cx=x+(int)(3.0*ran(1000000))-1;
		cy=y+(int)(3.0*ran(1000000))-1;
		cz=z+(int)(3.0*ran(1000000))-1;
		cx=bjX(cx);
		cy=bjY(cy);
		cz=bjZ(cz);
        //随机取出链单元周围的一个位置判断是否为空穴
		if(ii[cx][cy][cz]!=0)continue;

		/* judge the vacancy movable */
		//静态判定：移动后键不交错&部分动态先行判据
		if (cz==z&&cx!=x&&cy!=y)
		{
			if (ii[cx][y][z]==ii[x][cy][z]&&
					( abs(jj[cx][y][z]-jj[x][cy][z])==1 || abs(jj[cx][y][z]-jj[x][cy][z])==N-1) )
			continue; /*防止打断原有的键*/
			goto motion;}
		if (cy==y&&cx!=x&&cz!=z)
		{
			if (ii[cx][y][z]==ii[x][y][cz]&&
					( abs(jj[cx][y][z]-jj[x][y][cz])==1 || abs(jj[cx][y][z]-jj[x][y][cz])==N-1) )
			continue;
			goto motion;}
		if (cx==x&&cy!=y&&cz!=z)
		{
			if (ii[x][cy][z]==ii[x][y][cz]&&
					( abs(jj[x][cy][z]-jj[x][y][cz])==1 || abs(jj[x][cy][z]-jj[x][y][cz])==N-1) )
			continue;
			goto motion;}
        //有一维不变，转化为平面交叉判定
		if (cx!=x&&cy!=y&&cz!=z)
		if ( (ii[x][cy][cz]==ii[cx][y][z]&&
						( abs(jj[x][cy][cz]-jj[cx][y][z])==1 || abs(jj[x][cy][cz]-jj[cx][y][z])==N-1 ) )||
				(ii[cx][y][cz]==ii[x][cy][z]&&
						( abs(jj[cx][y][cz]-jj[x][cy][z])==1 || abs(jj[cx][y][cz]-jj[x][cy][z])==N-1 ) )||
				(ii[cx][cy][z]==ii[x][y][cz]&&
						( abs(jj[cx][cy][z]-jj[x][y][cz])==1 || abs(jj[cx][cy][z]-jj[x][y][cz])==N-1 ) ))
		continue;
        //三维均变化的判定

		/* motion */
		motion:
		/* the chosed bead is in middle of chain */
		j1=j-1;
		if(j1==0)j1=N;
		j2=j+1;
		if(j2==N+1)j2=1;
        //环形
		a=tfX(xx[i][j1]),b=tfY(yy[i][j1]),c=tfZ(zz[i][j1]);
		l=dist(a,b,c);
		xc=tfX(xx[i][j2]),yc=tfY(yy[i][j2]),zc=tfZ(zz[i][j2]);
		l1=dist(xc,yc,zc);
		if (l>1.8&&l1>1.8) /*需要同时拖动邻近的两个点，不允许*/
		continue;
		if (l<1.8&&l1<1.8)
		{ /*左右两个点都不需要动*/
			if (hindbend(a,b,c,x,y,z,(int)(l*l+0.2))==1)
			continue;
			if (hindbend(xc,yc,zc,x,y,z,(int)(l1*l1+0.2))==1)
			continue;
			xc=abjX(xx[i][j],cx);
			yc=abjY(yy[i][j],cy);
			zc=abjZ(zz[i][j],cz);


			l1=F*(xc-xx[i][j])/temp;
			if (l1<0&&ran(1000000)>exp(l1))
			continue;
			ii[cx][cy][cz]=i;
			jj[cx][cy][cz]=j;
			cx=tfX(xx[i][j]);
			cy=tfY(yy[i][j]);
			cz=tfZ(zz[i][j]);
			ii[cx][cy][cz]=0;
			jj[cx][cy][cz]=-1;
			xx[i][j]=xc;
			yy[i][j]=yc;
			zz[i][j]=zc;
			continue;
        }
		if (l>1.8&&l1<1.8)
		{ /*左边的点要跟着动*/
			if (hindbend(xc,yc,zc,x,y,z,(int)(l1*l1+0.2))==1)
			continue;
			p=fp(j,1,i);
			xc=abjX(xx[i][j],cx);
			yc=abjY(yy[i][j],cy);
			zc=abjZ(zz[i][j],cz);
			a=0;
			if(p==j)continue;


			c=0;
			c+=xc-xx[i][j];
			for(i1=j;i1!=p;i1=j2)
			{
				j2=i1-1;
				if(j2<1)j2+=N;
				c+=xx[i][i1]-xx[i][j2];
			}
			l1=F*c/temp;
			if (l1<0&&ran(1000000)>exp(l1))
			continue;
			ii[cx][cy][cz]=i; /*原来为空格的地方已经被链上的点填充，所以要把链数和链段数给它*/
			jj[cx][cy][cz]=j;
			cx=tfX(xx[i][p]); /*“p”是算动的点还是没动的点？（可能恰巧算动的点）*/
			cy=tfY(yy[i][p]);
			cz=tfZ(zz[i][p]); /*因为p动过了，所以原来p的位置现在是个空格*/
			ii[cx][cy][cz]=0;
			jj[cx][cy][cz]=-1;
			for(i1=p;i1!=j;i1=j2)
			{
				j2=i1+1;
				if(j2>N)j2-=N;
				xx[i][i1]=xx[i][j2];
				yy[i][i1]=yy[i][j2];
				zz[i][i1]=zz[i][j2];
				jj[tfX(xx[i][i1])][tfY(yy[i][i1])][tfZ(zz[i][i1])]=i1;
			}
			xx[i][j]=xc;
			yy[i][j]=yc;
			zz[i][j]=zc;
			continue;
        }
		if (l<1.8&&l1>1.8)
		{ /*左边不动右边动*/
			if (hindbend(a,b,c,x,y,z,(int)(l*l+0.2))==1)
			continue;
			p=fp(j,N,i);
			xc=abjX(xx[i][j],cx);
			yc=abjY(yy[i][j],cy);
			zc=abjZ(zz[i][j],cz);
			a=0;
			if(p==j)continue;


			c=0;
			c+=xc-xx[i][j];
			for(i1=j;i1!=p;i1=j2)
			{
				j2=i1+1;
				if(j2>N)j2-=N;
				c+=xx[i][i1]-xx[i][j2];
			}
			l1=F*c/temp;
			//l1=(E*b-a-d*R)/temp;
			if (l1<0&&ran(1000000)>exp(l1))
			continue;
			ii[cx][cy][cz]=i;
			jj[cx][cy][cz]=j;
			cx=tfX(xx[i][p]);
			cy=tfY(yy[i][p]);
			cz=tfZ(zz[i][p]);
			ii[cx][cy][cz]=0;
			jj[cx][cy][cz]=-1;
			for (i1=p;i1!=j;i1=j2)
			{
				j2=i1-1;
				if(j2<1)j2+=N;
				xx[i][i1]=xx[i][j2];
				yy[i][i1]=yy[i][j2];
				zz[i][i1]=zz[i][j2];
				jj[tfX(xx[i][i1])][tfY(yy[i][i1])][tfZ(zz[i][i1])]=i1;
			}
			xx[i][j]=xc;
			yy[i][j]=yc;
			zz[i][j]=zc;
			continue;
		}
	}

	/* display the run number and time */

	cycle++;


	//calculate the gyrational radius and statistic monomer density
	if(cycle%1==0)
	{


	//	printf("cycle=%i\n",cycle);
		for(i=1;i<=M;i++)
		{
			//calculate the mass center of single chain
			centx1=centx;
			centy1=centy;
			centz1=centz;

			centx=centy=centz=0.0;
			for(j=1;j<=N;j++)
			{
				centx+=xx[i][j];
				centy+=yy[i][j];
				centz+=zz[i][j];

			}

			centx/=N;
			centy/=N;
			centz/=N;
 /*           if (cycle-cycle/100*10000==0)
            cycle-cycle/100*10000==100;
            a=F*1000;
            b=(cycle-cycle/10000*10000)%100;
         	displace[a][b]=max(centx,centy,centz)-max(centx1,centy1,centz1);
         	*/
			//get the gyration radius in x,y,z directions
			gyration_x=gyration_y=gyration_z=0.0;
			maxj=minj=1;

			for(j=1;j<=N;j++)
			{
				gyration_x+=pow(xx[i][j]-centx,2);
				gyration_y+=pow(yy[i][j]-centy,2);
				gyration_z+=pow(zz[i][j]-centz,2);

				if (abs(xx[i][j]-centx)>abs(xx[i][maxj]-centx))
                    maxj=j;
			}

			minj=(maxj+N/2)%N;
			countt[maxj]++;
			/*
			infile=fopen(filename,"a");
			fprintf(infile,"%i\t%.3f\t%i\t%i\n",cycle,F,maxj,minj);
			fclose(infile);
			*/

			gyration_x/=N;
			gyration_y/=N;
			gyration_z/=N;


           // printf("%f\n",gyration_x);
			//add one sample, and sum the gyration radius
			gyration_sample_num++;
			gyration_x_sum+=gyration_x;
			gyration_y_sum+=gyration_y;
			gyration_z_sum+=gyration_z;
			gyration_sum+=gyration_x+gyration_y+gyration_z;


		}


	}

	//output an average gyration radius
	/*
	if(cycle%(Output*100)==0)
	{
		infile=fopen(F2,"a");
		fprintf(infile,"%i\t%.3f\t%.8f\t%.8f\t%.8f\t%.8f\n",cycle,F,gyration_x_sum/gyration_sample_num,gyration_y_sum/gyration_sample_num,gyration_z_sum/gyration_sample_num,gyration_sum/gyration_sample_num);
		fclose(infile);
		gyration_sample_num=0;
		gyration_x_sum=gyration_y_sum=gyration_z_sum=gyration_sum=0.0;
	}
	if(cycle%(Output*1)==0)
	{
		infile=fopen(F2,"a");
		for (i=1;i<=100;i++)
		{
			a=F*100;
		    fprintf(infile,"%i\t%.3f\t%.8f\n",cycle,F,displace[a][i]);
        }
	}
	if(cycle%(Output*100)==0)
	{
	    sprintf(filename,"Chain_T=%.2f_cycle=%i.ord",temp,cycle);
		infile=fopen(filename,"w");
		for(i=1;i<=M;i++)
		for(j=1;j<=N;j++)
		{
			fprintf(infile,"%i\t%i\t%i\n",xx[i][j],yy[i][j],zz[i][j]);
		}
		fclose(infile);
	}
	*/


	if ( cycle>(109999)  && cycle==(110000)  )  interval*=10;
	if  (cycle>120000)
        {
          if ( cycle>(99999)  && cycle%(100000)==0  ) interval*=10;
        }

	if( cycle>(9999)  && cycle%(10000)==0  )
    {
        sprintf(filename,"F=%.3f.dat",F);
        infile=fopen(filename,"a");
        fprintf(infile,"cycle\tNo\tF\tProbability\n");
        for(j=1;j<=N;j++)
        {
            fprintf(infile,"%i\t%i\t%.3f\t%.3f\n",cycle,j,F,(double)countt[j]/10000);
            countt[j]=0;
        }
        fclose(infile);
        F=F+direction*interval;

    }

	if (F>10) exit(1);
	goto start;
}

/* change the position to the initial cell */
int tfY(int x)
{
	if (x < 0)
		return (x + (1 - x / DY) * DY); /*??????????*/
	if (x % DY == 0)
		return (DY);
	return (x % DY);
}

int tfZ(int x)
{
	if (x < 0)
		return (x + (1 - x / DZ) * DZ); /*??????????*/
	if (x % DZ == 0)
		return (DZ);
	return (x % DZ);
}

int tfX(int x)
{
	if (x < 0)
		return (x + (1 - x / DX) * DX);
	if (x % DX == 0)
		return (DX);
	return (x % DX);
}

/* judge the range condition */
int bjY(int x)
{
	if (x > DY)
		x -= DY;
	else if (x < 1) /*X小于零的话也可以返回元胞*/
		x += DY;
	return (x);
}

int bjZ(int x)
{
	if (x > DZ)
		x -= DZ;
	else if (x < 1) /*X小于零的话也可以返回元胞*/
		x += DZ;
	return (x);
}

int bjX(int x)
{
	if (x > DX)
		x -= DX;
	else if (x < 1)
		x += DX;
	return (x);
}

/* judge the cell position */
int abjY(int x, int y)
{
	if (x < 1)
	{
		if (x % DY == 0 && y == 1)
			return (y + x / DY * DY);
		if (x % DY == 1 - DY && y == DY)
			return (y + (x / DY - 2) * DY);
		return (y + (x / DY - 1) * DY);
	}
	if (x % DY == 1 && y == DY)
		return (y + (x / DY - 1) * DY);
	if (x % DY == 0)
		if (y == DY || y == DY - 1)
			return (y + (x - 1) / DY * DY);
	return (y + x / DY * DY);
}

int abjZ(int x, int y)
{
	if (x < 1)
	{
		if (x % DZ == 0 && y == 1)
			return (y + x / DZ * DZ);
		if (x % DZ == 1 - DZ && y == DZ)
			return (y + (x / DZ - 2) * DZ);
		return (y + (x / DZ - 1) * DZ);
	}
	if (x % DZ == 1 && y == DZ)
		return (y + (x / DZ - 1) * DZ);
	if (x % DZ == 0)
		if (y == DZ || y == DZ - 1)
			return (y + (x - 1) / DZ * DZ);
	return (y + x / DZ * DZ);
}

int abjX(int x, int y)
{
	if (x < 1)
	{
		if (x % DX == 0 && y == 1)
			return (y + x / DX * DX);
		if (x % DX == 1 - DX && y == DX)
			return (y + (x / DX - 2) * DX);
		return (y + (x / DX - 1) * DX);
	}
	if (x % DX == 1 && y == DX)
		return (y + (x / DX - 1) * DX);
	if (x % DX == 0)
		if (y == DX || y == DX - 1)
			return (y + (x - 1) / DX * DX);
	return (y + x / DX * DX);
}

/* cal. the distance between vacancy and next bead */
double dist(int x, int y, int z)
{
	int xs, ys, zs;
	double xi, yi, zi;
	xs = abs(x - cx);
	if (xs > 2)
		xs = DX - xs; /*why?*/
	ys = abs(y - cy);
	if (ys > 2)
		ys = DY - ys;
	zs = abs(z - cz);
	if (zs > 2)
		zs = DZ - zs;
	xi = pow(xs, 2);
	yi = pow(ys, 2);
	zi = pow(zs, 2);
	return (sqrt(xi + yi + zi));
}

/* find the point to release */
int fp(int a, int b, int i)
{
	int i1, x, y, z, r, x1, x2, x3, y1, y2, y3, z1, z2, z3;
	int num, j1, j2, j3;
	if (b == N)
	{
		for (i1 = a, num = 1; num <= N - 2; i1++, num++)
		{
			j1 = i1;
			j2 = i1 + 1;
			j3 = i1 + 2;
			if (j1 > N)
				j1 -= N;
			if (j2 > N)
				j2 -= N;
			if (j3 > N)
				j3 -= N;

			x = xx[i][j1] - xx[i][j3];
			y = yy[i][j1] - yy[i][j3];
			z = zz[i][j1] - zz[i][j3];
			r = x * x + y * y + z * z;
			if (r > 3)
				continue;
			if (r == 1)
			{
				return (j2);
			}

			x1 = tfX(xx[i][j1]), x2 = tfX(xx[i][j2]), x3 = tfX(xx[i][j3]);
			y1 = tfY(yy[i][j1]), y2 = tfY(yy[i][j2]), y3 = tfY(yy[i][j3]);
			z1 = tfZ(zz[i][j1]), z2 = tfZ(zz[i][j2]), z3 = tfZ(zz[i][j3]);
			if (r == 2)
			{
				if (x == 0 && x1 != x2)
				{
					if (ii[x1][y3][z1] == ii[x1][y1][z3]
							&& /*防止形成的新键打断原来存在的旧键*/
							(abs(jj[x1][y3][z1] - jj[x1][y1][z3]) == 1
									|| abs(jj[x1][y3][z1] - jj[x1][y1][z3])
											== N - 1))
						continue;
					if (y2 == y1 && z2 == z3 && ii[x1][y1][z3] == ii[x2][y3][z1]
							&& (abs(jj[x1][y1][z3] - jj[x2][y3][z1]) == 1
									|| abs(jj[x1][y1][z3] - jj[x2][y3][z1])
											== N - 1)) /* 面对角线会打断体对角线！！！！(原来的一根旧键由一个面摆动到另一个面，会打断体对角线，这是不允许的运动）*/
						continue;
					if (y2 == y3 && z2 == z1 && ii[x1][y3][z1] == ii[x2][y1][z3]
							&& (abs(jj[x1][y3][z1] - jj[x2][y1][z3]) == 1
									|| abs(jj[x1][y3][z1] - jj[x2][y1][z3])
											== N - 1))
						continue;
					return (j2);
				}
				if (y == 0 && y1 != y2)
				{
					if (ii[x1][y1][z3] == ii[x3][y1][z1]
							&& (abs(jj[x1][y1][z3] - jj[x3][y1][z1]) == 1
									|| abs(jj[x1][y1][z3] - jj[x3][y1][z1])
											== N - 1))
						continue;
					if (x2 == x1 && z2 == z3 && ii[x1][y1][z3] == ii[x3][y2][z1]
							&& (abs(jj[x1][y1][z3] - jj[x3][y2][z1]) == 1
									|| abs(jj[x1][y1][z3] - jj[x3][y2][z1])
											== N - 1))
						continue;
					if (x2 == x3 && z2 == z1 && ii[x3][y1][z1] == ii[x1][y2][z3]
							&& (abs(jj[x3][y1][z1] - jj[x1][y2][z3]) == 1
									|| abs(jj[x3][y1][z1] - jj[x1][y2][z3])
											== N - 1))
						continue;
					return (j2);
				}
				if (z == 0 && z1 != z2)
				{
					if (ii[x1][y3][z1] == ii[x3][y1][z1]
							&& (abs(jj[x1][y3][z1] - jj[x3][y1][z1]) == 1
									|| abs(jj[x1][y3][z1] - jj[x3][y1][z1])
											== N - 1))
						continue;
					if (x2 == x1 && y2 == y3 && ii[x1][y3][z1] == ii[x3][y1][z2]
							&& (abs(jj[x1][y3][z1] - jj[x3][y1][z2]) == 1
									|| abs(jj[x1][y3][z1] - jj[x3][y1][z2])
											== N - 1))
						continue;
					if (x2 == x3 && y2 == y1 && ii[x3][y1][z1] == ii[x1][y3][z2]
							&& (abs(jj[x3][y1][z1] - jj[x1][y3][z2]) == 1
									|| abs(jj[x3][y1][z1] - jj[x1][y3][z2])
											== N - 1))
						continue;
					return (j2);
				}
				return (j2);
			}
			if (r == 3)
			{
				if ((ii[x1][y3][z3] == ii[x3][y1][z1]
						&& (abs(jj[x1][y3][z3] - jj[x3][y1][z1]) == 1
								|| abs(jj[x1][y3][z3] - jj[x3][y1][z1]) == N - 1))
						|| (ii[x3][y1][z3] == ii[x1][y3][z1]
								&& (abs(jj[x3][y1][z3] - jj[x1][y3][z1]) == 1
										|| abs(jj[x3][y1][z3] - jj[x1][y3][z1])
												== N - 1))
						|| (ii[x3][y3][z1] == ii[x1][y1][z3]
								&& (abs(jj[x3][y3][z1] - jj[x1][y1][z3]) == 1
										|| abs(jj[x3][y3][z1] - jj[x1][y1][z3])
												== N - 1)))
					continue; /*防止体对角线互相打断*/
				return (j2);
			}
		}
		return (a);
	}
	for (i1 = a, num = 1; num <= N - 2; i1--, num++)
	{
		j1 = i1;
		j2 = i1 - 1;
		j3 = i1 - 2;
		if (j1 < 1)
			j1 += N;
		if (j2 < 1)
			j2 += N;
		if (j3 < 1)
			j3 += N;

		x = xx[i][j1] - xx[i][j3];
		y = yy[i][j1] - yy[i][j3];
		z = zz[i][j1] - zz[i][j3];
		r = x * x + y * y + z * z;
		if (r > 3)
			continue;
		if (r == 1)
			return (j2);
		x1 = tfX(xx[i][j1]), x2 = tfX(xx[i][j2]), x3 = tfX(xx[i][j3]);
		y1 = tfY(yy[i][j1]), y2 = tfY(yy[i][j2]), y3 = tfY(yy[i][j3]);
		z1 = tfZ(zz[i][j1]), z2 = tfZ(zz[i][j2]), z3 = tfZ(zz[i][j3]);
		if (r == 2)
		{
			if (x == 0 && x1 != x2)
			{
				if (ii[x1][y3][z1] == ii[x1][y1][z3]
						&& (abs(jj[x1][y3][z1] - jj[x1][y1][z3]) == 1
								|| abs(jj[x1][y3][z1] - jj[x1][y1][z3]) == N - 1))
					continue;
				if (y2 == y1 && z2 == z3 && ii[x1][y1][z3] == ii[x2][y3][z1]
						&& (abs(jj[x1][y1][z3] - jj[x2][y3][z1]) == 1
								|| abs(jj[x1][y1][z3] - jj[x2][y3][z1]) == N - 1))
					continue;
				if (y2 == y3 && z2 == z1 && ii[x1][y3][z1] == ii[x2][y1][z3]
						&& (abs(jj[x1][y3][z1] - jj[x2][y1][z3]) == 1
								|| abs(jj[x1][y3][z1] - jj[x2][y1][z3]) == N - 1))
					continue;
				return (j2);
			}
			if (y == 0 && y1 != y2)
			{
				if (ii[x1][y1][z3] == ii[x3][y1][z1]
						&& (abs(jj[x1][y1][z3] - jj[x3][y1][z1]) == 1
								|| abs(jj[x1][y1][z3] - jj[x3][y1][z1]) == N - 1))
					continue;
				if (x2 == x1 && z2 == z3 && ii[x1][y1][z3] == ii[x3][y2][z1]
						&& (abs(jj[x1][y1][z3] - jj[x3][y2][z1]) == 1
								|| abs(jj[x1][y1][z3] - jj[x3][y2][z1]) == N - 1))
					continue;
				if (x2 == x3 && z2 == z1 && ii[x3][y1][z1] == ii[x1][y2][z3]
						&& (abs(jj[x3][y1][z1] - jj[x1][y2][z3]) == 1
								|| abs(jj[x3][y1][z1] - jj[x1][y2][z3]) == N - 1))
					continue;
				return (j2);
			}
			if (z == 0 && z1 != z2)
			{
				if (ii[x1][y3][z1] == ii[x3][y1][z1]
						&& (abs(jj[x1][y3][z1] - jj[x3][y1][z1]) == 1
								|| abs(jj[x1][y3][z1] - jj[x3][y1][z1]) == N - 1))
					continue;
				if (x2 == x1 && y2 == y3 && ii[x1][y3][z1] == ii[x3][y1][z2]
						&& (abs(jj[x1][y3][z1] - jj[x3][y1][z2]) == 1
								|| abs(jj[x1][y3][z1] - jj[x3][y1][z2]) == N - 1))
					continue;
				if (x2 == x3 && y2 == y1 && ii[x3][y1][z1] == ii[x1][y3][z2]
						&& (abs(jj[x3][y1][z1] - jj[x1][y3][z2]) == 1
								|| abs(jj[x3][y1][z1] - jj[x1][y3][z2]) == N - 1))
					continue;
				return (j2);
			}
			return (j2);
		}
		if (r == 3)
		{
			if ((ii[x1][y3][z3] == ii[x3][y1][z1]
					&& (abs(jj[x1][y3][z3] - jj[x3][y1][z1]) == 1
							|| abs(jj[x1][y3][z3] - jj[x3][y1][z1]) == N - 1))
					|| (ii[x3][y1][z3] == ii[x1][y3][z1]
							&& (abs(jj[x3][y1][z3] - jj[x1][y3][z1]) == 1
									|| abs(jj[x3][y1][z3] - jj[x1][y3][z1])
											== N - 1))
					|| (ii[x3][y3][z1] == ii[x1][y1][z3]
							&& (abs(jj[x3][y3][z1] - jj[x1][y1][z3]) == 1
									|| abs(jj[x3][y3][z1] - jj[x1][y1][z3])
											== N - 1)))
				continue;
			return (j2);
		}
	}
	return (a);
}

int hindbend(int a, int b, int c, int x, int y, int z, int l)
{

	int i0, j0, i1, j1, i2, j2;

	i0 = ii[x][y][z];
	j0 = jj[x][y][z];

	if (l == 3)//立方对角线
	{
		i1 = ii[a][cy][cz];
		j1 = jj[a][cy][cz];
		i2 = ii[cx][b][c];
		j2 = jj[cx][b][c];
		if (i1 != i0 || j1 != j0)
			if (i2 != i0 || j2 != j0)
			{
				if (i1 == i2 && (abs(j1 - j2) == 1 || abs(j1 - j2) == N - 1))
					return (1);
			}

		i1 = ii[cx][b][cz];
		j1 = jj[cx][b][cz];
		i2 = ii[a][cy][c];
		j2 = jj[a][cy][c];
		if (i1 != i0 || j1 != j0)
			if (i2 != i0 || j2 != j0)
			{
				if (i1 == i2 && (abs(j1 - j2) == 1 || abs(j1 - j2) == N - 1))
					return (1);
			}
		i1 = ii[cx][cy][c];
		j1 = jj[cx][cy][c];
		i2 = ii[a][b][cz];
		j2 = jj[a][b][cz];
		if (i1 != i0 || j1 != j0)
			if (i2 != i0 || j2 != j0)
			{
				if (i1 == i2 && (abs(j1 - j2) == 1 || abs(j1 - j2) == N - 1))
					return (1);
			}
		return (0);

	}

	if (l == 2)
	{
		if (cx == a && cx != x)
		{
			if (abs(ii[a][b][cz] - ii[a][cy][c]) == 0
					&& (abs(jj[a][b][cz] - jj[a][cy][c]) == 1
							|| abs(jj[a][b][cz] - jj[a][cy][c]) == N - 1))
				return (1);
			if (y == b && z == cz && abs(ii[a][b][cz] - ii[x][cy][c]) == 0
					&& (abs(jj[a][b][cz] - jj[x][cy][c]) == 1
							|| abs(jj[a][b][cz] - jj[x][cy][c]) == N - 1))
				return (1);
			if (y == cy && z == c && abs(ii[a][cy][c] - ii[x][b][cz]) == 0
					&& (abs(jj[a][cy][c] - jj[x][b][cz]) == 1
							|| abs(jj[a][cy][c] - jj[x][b][cz]) == N - 1))
				return (1);
		}
		if (cy == b && cy != y)
		{
			if (abs(ii[a][b][cz] - ii[cx][b][c]) == 0
					&& (abs(jj[a][b][cz] - jj[cx][b][c]) == 1
							|| abs(jj[a][b][cz] - jj[cx][b][c]) == N - 1))
				return (1);
			if (x == a && z == cz && abs(ii[a][b][cz] - ii[cx][y][c]) == 0
					&& (abs(jj[a][b][cz] - jj[cx][y][c]) == 1
							|| abs(jj[a][b][cz] - jj[cx][y][c]) == N - 1))
				return (1);
			if (x == cx && z == c && abs(ii[cx][b][c] - ii[a][y][cz]) == 0
					&& (abs(jj[cx][b][c] - jj[a][y][cz]) == 1
							|| abs(jj[cx][b][c] - jj[a][y][cz]) == N - 1))
				return (1);
		}
		if (cz == c && cz != z)
		{
			if (abs(ii[a][cy][c] - ii[cx][b][c]) == 0
					&& (abs(jj[a][cy][c] - jj[cx][b][c]) == 1
							|| abs(jj[a][cy][c] - jj[cx][b][c]) == N - 1))
				return (1);
			if (x == a && y == cy && abs(ii[a][cy][c] - ii[cx][b][z]) == 0
					&& (abs(jj[a][cy][c] - jj[cx][b][z]) == 1
							|| abs(jj[a][cy][c] - jj[cx][b][z]) == N - 1))
				return (1);
			if (x == cx && y == b && abs(ii[cx][b][c] - ii[a][cy][z]) == 0
					&& (abs(jj[cx][b][c] - jj[a][cy][z]) == 1
							|| abs(jj[cx][b][c] - jj[a][cy][z]) == N - 1))
				return (1);
		}
		return (0);
	}
	return (0);
}

/* judge the interaction energy (if near beads neibering) *//*是判断与一根键相邻的健数吧？（是不是最多是8个?)*/
int je(int x1, int y1, int z1, int x2, int y2, int z2)
{
	int ii1, ii2, jj1, jj2;
	int xs, ys, zs, xe, ye, ze;
	int u, v, w, c = 0;
	x1 = tfX(x1);
	y1 = tfY(y1);
	z1 = tfZ(z1);
	x2 = tfX(x2);
	y2 = tfY(y2);
	z2 = tfZ(z2);
	for (u = -1; u <= 1; u++)
		for (v = -1; v <= 1; v++)
			for (w = -1; w <= 1; w++)
			{ /*三个for循环，将旧键在空间中进行了平移*/
				if (u == 0 && v == 0 && w == 0)
					continue;
				xs = bjX(x1 + u), ys = bjY(y1 + v), zs = bjY(z1 + w);
				xe = bjX(x2 + u), ye = bjZ(y2 + v), ze = bjZ(z2 + w);
				if (xs == x2 && ys == y2 && zs == z2)
					continue;
				if (xe == x1 && ye == y1 && ze == z1)
					continue; /*防止找到的键与原来的键接在一起?*/
				ii1 = ii[xs][ys][zs];
				ii2 = ii[xe][ye][ze];
				jj1 = jj[xs][ys][zs];
				jj2 = jj[xe][ye][ze];
				if (ii1 == ii2
						&& (abs(jj1 - jj2) == 1 || abs(jj1 - jj2) == N - 1))
					c++;
			}
	return (c);
}

/* judge the part of conformation*/
int jc(int c, int i)
{
	int b;
	int c1, c2, c3, c4;
	c1 = c - 2;
	if (c1 < 1)
		c1 += N;
	c2 = c - 1;
	if (c2 < 1)
		c2 += N;
	c3 = c + 1;
	if (c3 > N)
		c3 -= N;
	c4 = c + 2;
	if (c4 > N)
		c4 -= N;
	b = ((xx[i][c1] - xx[i][c2]) != (xx[i][c2] - xx[i][c3])
			|| (yy[i][c1] - yy[i][c2]) != (yy[i][c2] - yy[i][c3])
			|| (zz[i][c1] - zz[i][c2]) != (zz[i][c2] - zz[i][c3]));
	b += ((xx[i][c2] - xx[i][c3]) != (xx[i][c3] - xx[i][c4])
			|| (yy[i][c2] - yy[i][c3]) != (yy[i][c3] - yy[i][c4])
			|| (zz[i][c3] - zz[i][c3]) != (zz[i][c3] - zz[i][c4]));
	b -= ((xx[i][c1] - xx[i][c2]) != (xx[i][c2] - xx[i][c])
			|| (yy[i][c1] - yy[i][c2]) != (yy[i][c2] - yy[i][c])
			|| (zz[i][c1] - zz[i][c2]) != (zz[i][c2] - zz[i][c]));
	b -= ((xx[i][c4] - xx[i][c3]) != (xx[i][c3] - xx[i][c])
			|| (yy[i][c4] - yy[i][c3]) != (yy[i][c3] - yy[i][c])
			|| (zz[i][c4] - zz[i][c3]) != (zz[i][c3] - zz[i][c]));
	b--; /*看主程序对jc函数的调用可猜想，c这个点是kink点，所以(c-1),c,(c+1)的构象是旁氏构想*/
	return (b);
}

double ran(long t) /*generate 2*10**18 sequential random numbers (from 0 to 1.0-1.2*exp(-7.0)) by negative seed t to initiallize,*/
	                    /*p282 Numerical Recipes in C 2nd ed. 1992 Cambridge University Press,London, Press WH, Teukolsky SA,Vetterling WT, Flannery BP*/
 {

	int j;
	long int k;
	static long idum2 = 123456789;
	static long iy = 0;
	static long iv[32];
	double temp;

	if (t <= 0)
	{
		if (0 - t < 1)
			t = 1;
		else
			t = 0 - t;
		idum2 = t;
		for (j = 39; j >= 0; j--)
		{
			k = t / 53668;
			t = 40014 * (t - k * 53668) - k * 12211;
			if (t < 0)
				t += 2147483563;
			if (j < 32)
				iv[j] = t;
		}
		iy = iv[0];
	}
	k = t / 53668;
	t = 40014 * (t - k * 53668) - k * 12211;
	if (t < 0)
		t += 2147483563;
	k = idum2 /52774;
	idum2 = 40692 * (idum2 - k * 52774) - k * 3791;
	if (idum2 < 0)
		idum2 += 2147483399;
	j = iy / (1 + 2147483562 / 32);
	iy = iv[j] - idum2;
	iv[j] = t;
	if (iy < 0)
		iy += 2147483562;
	temp = 1.0 * iy / 2147483563;
	return (temp);
}

int max(int	x,int	y,int	z)
{     int a,b,c;
       a=x;
       b=y;
       c=z;
       if (a>=b&&a>=c)
       return x;
       if (b>a&&b>=c)
       return y;
       if (c>a&&c>b)
       return z;
}
