#include <iostream>
#include <iomanip>
#include <cmath>
#include <fstream>
#include <cstdlib>
#include <vector>
#include <ctime>

using namespace std;
double risk_free_rate, strike_price, initial_stock_price, expiration_time, volatility, q;
int method,monitor;
int x10, x11, x12, x20, x21, x22;
int no_of_trials;
double sample_mean, sample_mean_square;
double se;
float computational_time;
double efficiency;
double call_price_MS;
int option_price[2] = {0,0};
double **P;


#define m1 2147483647
#define m2 2145483479
#define a12 63308
#define a13 -183326
#define a21 86098
#define a23 -539608
#define q12 33921
#define q13 11714
#define q21 24919
#define q23 3976
#define r12 12979
#define r13 2883
#define r21 7417
#define r23 2071
#define Invmp1 4.656612873077393e-10;

/* Frances Y. Kuo
 //
 // Email: <f.kuo@unsw.edu.au>
 // School of Mathematics and Statistics
 // University of New South Wales
 // Sydney NSW 2052, Australia
 //
 // Last updated: 21 October 2008
 //
 //   You may incorporate this source code into your own program
 //   provided that you
 //   1) acknowledge the copyright owner in your program and publication
 //   2) notify the copyright owner by email
 //   3) offer feedback regarding your experience with different direction numbers
 //
 //
 // -----------------------------------------------------------------------------
 // Licence pertaining to sobol.cc and the accompanying sets of direction numbers
 // -----------------------------------------------------------------------------
 // Copyright (c) 2008, Frances Y. Kuo and Stephen Joe
 // All rights reserved.
 //
 // Redistribution and use in source and binary forms, with or without
 // modification, are permitted provided that the following conditions are met:
 //
 //     * Redistributions of source code must retain the above copyright
 //       notice, this list of conditions and the following disclaimer.
 //
 //     * Redistributions in binary form must reproduce the above copyright
 //       notice, this list of conditions and the following disclaimer in the
 //       documentation and/or other materials provided with the distribution.
 //
 //     * Neither the names of the copyright holders nor the names of the
 //       University of New South Wales and the University of Waikato
 //       and its contributors may be used to endorse or promote products derived
 //       from this software without specific prior written permission.
 //
 // THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS ``AS IS'' AND ANY
 // EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 // WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 // DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE LIABLE FOR ANY
 // DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 // (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 // LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 // ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 // (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 // SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
double **sobol_points(unsigned N, unsigned D, char *dir_file)
{
    ifstream infile(dir_file,ios::in);
    if (!infile) {
        cout << "Input file containing direction numbers cannot be found!\n";
        exit(1);
    }
    char buffer[1000];
    infile.getline(buffer,1000,'\n');
    
    // L = max number of bits needed
    unsigned L = (unsigned)ceil(log((double)N)/log(2.0));
    
    // C[i] = index from the right of the first zero bit of i
    unsigned *C = new unsigned [N];
    C[0] = 1;
    for (unsigned i=1;i<=N-1;i++) {
        C[i] = 1;
        unsigned value = i;
        while (value & 1) {
            value >>= 1;
            C[i]++;
        }
    }
    
    // POINTS[i][j] = the jth component of the ith point
    //                with i indexed from 0 to N-1 and j indexed from 0 to D-1
    double **POINTS = new double * [N];
    for (unsigned i=0;i<=N-1;i++) POINTS[i] = new double [D];
    for (unsigned j=0;j<=D-1;j++) POINTS[0][j] = 0;
    
    // ----- Compute the first dimension -----
    
    // Compute direction numbers V[1] to V[L], scaled by pow(2,32)
    unsigned *V = new unsigned [L+1];
    for (unsigned i=1;i<=L;i++) V[i] = 1 << (32-i); // all m's = 1
    
    // Evalulate X[0] to X[N-1], scaled by pow(2,32)
    unsigned *X = new unsigned [N];
    X[0] = 0;
    for (unsigned i=1;i<=N-1;i++) {
        X[i] = X[i-1] ^ V[C[i-1]];
        POINTS[i][0] = (double)X[i]/pow(2.0,32); // *** the actual points
        //        ^ 0 for first dimension
    }
    
    // Clean up
    delete [] V;
    delete [] X;
    
    
    // ----- Compute the remaining dimensions -----
    for (unsigned j=1;j<=D-1;j++) {
        
        // Read in parameters from file
        unsigned d, s;
        unsigned a;
        infile >> d >> s >> a;
        unsigned *m = new unsigned [s+1];
        for (unsigned i=1;i<=s;i++) infile >> m[i];
        
        // Compute direction numbers V[1] to V[L], scaled by pow(2,32)
        unsigned *V = new unsigned [L+1];
        if (L <= s) {
            for (unsigned i=1;i<=L;i++) V[i] = m[i] << (32-i);
        }
        else {
            for (unsigned i=1;i<=s;i++) V[i] = m[i] << (32-i);
            for (unsigned i=s+1;i<=L;i++) {
                V[i] = V[i-s] ^ (V[i-s] >> s);
                for (unsigned k=1;k<=s-1;k++)
                    V[i] ^= (((a >> (s-1-k)) & 1) * V[i-k]);
            }
        }
        
        // Evalulate X[0] to X[N-1], scaled by pow(2,32)
        unsigned *X = new unsigned [N];
        X[0] = 0;
        for (unsigned i=1;i<=N-1;i++) {
            X[i] = X[i-1] ^ V[C[i-1]];
            POINTS[i][j] = (double)X[i]/pow(2.0,32); // *** the actual points
            //        ^ j for dimension (j+1)
        }
        
        // Clean up
        delete [] m;
        delete [] V;
        delete [] X;
    }
    delete [] C;
    
    return POINTS;
}


double max(double a, double b) {
    return (b < a) ? a : b;
}

double N(const double& z) {
    if (z > 6.0) { return 1.0; }; // this guards against overflow
    if (z < -6.0) { return 0.0; };
    double b1 = 0.31938153;
    double b2 = -0.356563782;
    double b3 = 1.781477937;
    double b4 = -1.821255978;
    double b5 = 1.330274429;
    double p = 0.2316419;
    double c2 = 0.3989423;
    double a = fabs(z);
    double t = 1.0 / (1.0 + a*p);
    double b = c2*exp((-z)*(z / 2.0));
    double n = ((((b5*t + b4)*t + b3)*t + b2)*t + b1)*t;
    n = 1.0 - b*n;
    if (z < 0.0) n = 1.0 - n;
    return n;
}

int Random()
{
    
    int h, p12, p13, p21, p23;
    /* Component 1 */
    h = x10/q13;
    p13 = -a13*(x10-h*q13)-h*r13;
    h = x11/q12;
    p12 = a12*(x11-h*q12)-h*r12;
    if(p13<0)
        p13 = p13+m1;
    if(p12<0)
        p12 = p12+m1;
    x10 = x11;
    x11 = x12;
    x12 = p12-p13;
    if(x12<0)
        x12 = x12+m1; /* Component 2 */
    h = x20/q23;
    p23 = -a23*(x20-h*q23)-h*r23;
    h = x22/q21;
    p21 = a21*(x22-h*q21)-h*r21;
    if(p23<0)
        p23 = p23+m2;
    if(p21<0)
        p21 = p21+m2;
    x20 = x21;
    x21 = x22;
    x22 = p21-p23;
    if(x22<0)
        x22=x22+m2;
    if (x12<x22)
        return (x12-x22+m1);
    else
        return (x12-x22);
}



double get_uniform(){
    int Z;
    Z = Random();
    if(Z == 0)
        Z=m1;
    return Z*Invmp1;
}

double get_gaussian(){
    
    return (sqrt(-2.0*log(get_uniform()))*cos(6.283185307999998*get_uniform()));
}

double get_gaussian_inverse_transform(double uniform){
    
    double a0 = 2.50662823884;
    double a1 = -18.61500062529;
    double a2 =41.39119773534;
    double a3 =-25.44106049637;
    double b0 = -8.47351093090;
    double b1 =23.08336743743;
    double b2 =-21.06224101826;
    double b3 = 3.13082909833;
    double c0 =0.3374754822726147;
    double c1 =0.9761690190917186;
    double c2 =0.1607979714918209;
    double c3 =0.0276438810333863;
    double c4 =0.0038405729373609;
    double c5 =0.0003951896511919;
    double c6 =0.0000321767881768;
    double c7 =0.0000002888167364;
    double c8 =0.0000003960315187;
    double u = uniform;
    
    double y = u - 0.5;
    double x;
    double r;
    if (abs(y)<0.42){
        r = y*y;
        x = y*(((a3*r + a2)*r + a1)*r + a0) / ((((b3*r + b2)*r + b1)*r + b0)*r + 1);
    }
    else{
        r = u;
        if (y>0)
            r = 1 - u;
        r = log(-log(r));
        x = c0 + r*(c1 + r*(c2 + r*(c3 + r*(c4 + r*(c5 + r*(c6 + r*(c7 + r*c8)))))));
        if (y<0)
            x = -1 * x;
    }
    x = x - (N(x) - u) / (exp(-0.5*x*x + 0.918938533204672));
    return x;
}



double option_price_call_black_scholes(const double& S,       // spot (underlying) price
                                       const double& K,       // strike (exercise) price,
                                       const double& r,       // interest rate
                                       const double& q,       //dividends
                                       const double& sigma,   // volatility
                                       const double& time) {  // time to maturity
    double time_sqrt = sqrt(time);
    double d1 = (log(S / K) + (r-q)*time) / (sigma*time_sqrt) + 0.5*sigma*time_sqrt; //formula from lecture notes one.
    double d2 = d1 - (sigma*time_sqrt);
    return S*exp(-q*time)*N(d1)- K*exp(-r*time)*N(d2);
}



double option_price_call_monte_carlo_simulaion(const double& no_of_trails,
                                               const double& S,
                                               const double& K,
                                               const double& r,
                                               const double& v,
                                               const double& q,
                                               const double& time,
                                               const int& m
                                               ){
    
    
    double temp = get_gaussian();
    double S_bar, S_k;
    double x_bar, y_bar;
    double x_k;
    double S_1;
    
    temp = get_gaussian();
    S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
    S_k = S_1;
    S_bar = S_1/m;
    for (int k = 2; k <= m; k++){
        temp = get_gaussian();
        S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_bar = S_bar + S_k/m;
    }
    x_bar = max(S_bar-K,0.0)*exp(-r*time);
    y_bar = x_bar*x_bar;
    for (int k = 2; k <= no_of_trails; k++){
        temp = get_gaussian();
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_bar = S_1/m;
        for (int j = 2; j <= m; j++){
            temp = get_gaussian();
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_bar = S_bar + S_k/m;
        }
        x_k = max(S_bar-K,0.0)*exp(-r*time);
        x_bar = (1.0 - 1.0 / k)*x_bar + x_k / k;
        y_bar = (1.0 - 1.0 / k)*y_bar + x_k*x_k / k;
    }
    sample_mean = x_bar;
    sample_mean_square = y_bar;
    return sample_mean;
}



double standard_error(const int& sample_size){
    return sqrt((1.0 / (sample_size - 1.0))*(sample_mean_square - sample_mean*sample_mean));
}

double control_variates(const double& no_of_trails,
                        const double& S,
                        const double& K,
                        const double& r,
                        const double& v,
                        const double& q,
                        const double& time,
                        const int& m
                        ){
    double x_bar, y_bar;
    double S_t, S_k, S_t_hat,temp;
    double v_hat_square = (2*m + 1)*v*v/(3*m);
    double q_hat = q+0.5*v*v - 0.5*v_hat_square;
    double t_hat = 0.5*(time + 1.0/m);
    double b = 0;
    double S_1;
    double delta = time/m;
    double gaussian_sum;
    double S_t_hat_hat;
    int j = 10000;
    double tempx[j], tempy[j];
    
    temp = get_gaussian();
    gaussian_sum = sqrt(delta)*temp;
    S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
    S_t = S_1/m;
    S_k = S_1;
    S_t_hat_hat = pow(S_1,1.0/m);
    for (int k = 2; k <= m; k++){
        temp = get_gaussian();
        S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_t_hat_hat = S_t_hat_hat*pow(S_k, 1.0/m);
        S_t = S_t + S_k/m;
    }
    tempy[0] = max((S_t-K),0.0);
    tempx[0] = max((S_t_hat_hat-K),0.0);
    x_bar = tempx[0];
    y_bar = tempy[0];
    //cout<<tempy[0]<<"~~~"<<endl<<tempx[0]<<endl;
    
    for(int i = 2; i<=j; i++){
        temp = get_gaussian();
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_t = S_1/m;
        S_t_hat_hat = pow(S_1,1.0/m);
        //gaussian_sum = sqrt(delta)*temp;
        for (int k = 2; k <= m; k++){
            temp = get_gaussian();
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_t_hat_hat = S_t_hat_hat*pow(S_k, 1.0/m);
            //gaussian_sum = gaussian_sum + k*sqrt(delta)*temp;
            S_t = S_t + S_k/m;
        }
        //S_t_hat = S*exp((r-q-0.5*v*v)*t_hat + v*gaussian_sum/m);
        tempy[i-1] = max((S_t-K),0.0);
        tempx[i-1] = max((S_t_hat_hat-K),0.0);
        y_bar = (1.0 - 1.0 / i)*y_bar + tempy[i-1] / i;
        x_bar = (1.0 - 1.0 / i)*x_bar + tempx[i-1] / i;
    }
    
    double z_1,z_2,z_3;
    z_1 = z_2 = z_3 = 0;
    for(int i = 0; i<j;i++)
    {
        z_1 = z_1 + (tempx[i] - x_bar)*(tempy[i] - y_bar);
        z_2 = z_2 + (tempx[i] - x_bar)*(tempx[i] - x_bar);
        z_3 = z_3 + (tempy[i] - y_bar)*(tempy[i] - y_bar);
        
    }
    b = z_1/z_2;
    //cout<< "correlation = "<< z_1/sqrt(z_2*z_3) <<endl;
    //cout<< "b ="<<b<<endl;
    
    double E_X = option_price_call_black_scholes(S, K, r, q_hat, sqrt(v_hat_square),t_hat)*exp(r*t_hat);
    //cout<<"E_X ="<< E_X<<"!!!!!!!!!!!!!!"<<endl;
    
    double Y_bar, Y_bar_square;
    double Y_k;
    double x_k, y_k;
    
    temp = get_gaussian();
    S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
    S_k = S_1;
    S_t = S_1/m;
    S_t_hat = pow(S_1,1.0/m);
    for (int k = 2; k <= m; k++){
        temp = get_gaussian();
        S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_t_hat = S_t_hat*pow(S_k, 1.0/m);
        S_t = S_t + S_k/m;
    }
    y_k = max((S_t-K),0.0);
    x_k = max((S_t_hat-K),0.0);
    Y_k = (y_k + b*(E_X - x_k));
    Y_bar = Y_k;
    Y_bar_square = Y_bar*Y_bar;
    
    for(int i = 2; i<=no_of_trails; i++){
        temp = get_gaussian();
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_t = S_1/m;
        S_t_hat = pow(S_1,1.0/m);
        for (int k = 2; k <= m; k++){
            temp = get_gaussian();
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_t_hat = S_t_hat*pow(S_k, 1.0/m);
            S_t = S_t + S_k/m;
        }
        y_k = max((S_t-K),0.0);
        x_k = max((S_t_hat-K),0.0);
        
        Y_k = (y_k + b*(E_X - x_k))*exp(-r*time);
        Y_bar = (1.0 - 1.0 / i)*Y_bar + Y_k / i;
        Y_bar_square = (1.0 - 1.0 / i)*Y_bar_square + Y_k*Y_k / i;
    }
    sample_mean = Y_bar;
    sample_mean_square = Y_bar_square;
    return sample_mean;
}

double random_shift(int N, int D)
{
    for (int j=0;j<=D-1;j++){
        double u = get_uniform();
        for (int i=0;i<=N-1;i++) {
            P[i][j] = (P[i][j]+u < 1.0) ? P[i][j]+u : P[i][j]+u-1.0;
        }
    }
    return 0.0;
}

double QMC_asian_call(  const double& S,
                      const double& K,
                      const double& r,
                      const double& v,
                      const double& q,
                      const double& time,
                      const int& m,
                      const int& no_of_trails,
                      const int& L
                      ){
    
    
    double temp;
    double S_bar, S_k;
    double x_bar;
    double x_k;
    double S_1;
    double X_BAR,Y_BAR;
    
    char x[8] = "sob.txt";
    int N = no_of_trails;
    int D = m;
    P = sobol_points(N+1,D,x);
    
    random_shift(N+1, D);
    temp = get_gaussian_inverse_transform(P[1][0]);
    S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
    S_k = S_1;
    S_bar = S_1/m;
    for (int k = 2; k <= m; k++){
        temp = get_gaussian_inverse_transform(P[1][k-1]);
        S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_bar = S_bar + S_k/m;
    }
    x_bar = max(S_bar-K,0.0)*exp(-r*time);
    //y_bar = x_bar*x_bar;
    for (int k = 2; k <= no_of_trails; k++){
        temp = get_gaussian_inverse_transform(P[k][0]);
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_bar = S_1/m;
        for (int j = 2; j <= m; j++){
            temp = get_gaussian_inverse_transform(P[k][j-1]);
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_bar = S_bar + S_k/m;
        }
        x_k = max(S_bar-K,0.0)*exp(-r*time);
        x_bar = (1.0 - 1.0 / k)*x_bar + x_k / k;
        //y_bar = (1.0 - 1.0 / k)*y_bar + x_k*x_k / k;
    }
    X_BAR = x_bar;
    Y_BAR = x_bar*x_bar;
    
    for(int pp=1;pp<L;pp++){
        random_shift(N+1, D);
        temp = get_gaussian_inverse_transform(P[1][0]);
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_bar = S_1/m;
        for (int k = 2; k <= m; k++){
            temp = get_gaussian_inverse_transform(P[1][k-1]);
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_bar = S_bar + S_k/m;
        }
        x_bar = max(S_bar-K,0.0)*exp(-r*time);
        //y_bar = x_bar*x_bar;
        for (int k = 2; k <= no_of_trails; k++){
            temp = get_gaussian_inverse_transform(P[k][0]);
            S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_k = S_1;
            S_bar = S_1/m;
            for (int j = 2; j <= m; j++){
                temp = get_gaussian_inverse_transform(P[k][j-1]);
                S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
                S_bar = S_bar + S_k/m;
            }
            x_k = max(S_bar-K,0.0)*exp(-r*time);
            x_bar = (1.0 - 1.0 / k)*x_bar + x_k / k;
            //y_bar = (1.0 - 1.0 / k)*y_bar + x_k*x_k / k;
        }
        X_BAR = (1.0 - 1.0 / pp)*X_BAR + x_bar / pp;
        Y_BAR = (1.0 - 1.0 / pp)*Y_BAR + x_bar*x_bar / pp;
    }
    sample_mean = X_BAR;
    sample_mean_square = Y_BAR;
    return sample_mean;
}

double QMC_asian_call_Control(  const double& S,
                              const double& K,
                              const double& r,
                              const double& v,
                              const double& q,
                              const double& time,
                              const int& m,
                              const int& no_of_trails,
                              const int& L
                              ){
    
    double x_bar, y_bar;
    double S_t, S_k, S_t_hat,temp;
    double v_hat_square = (2*m + 1)*v*v/(3*m);
    double q_hat = q+0.5*v*v - 0.5*v_hat_square;
    double t_hat = 0.5*(time + 1.0/m);
    double b = 0;
    double S_1;
    double delta = time/m;
    double gaussian_sum;
    double S_t_hat_hat;
    int j = 10000;
    double X_BAR,Y_BAR;
    double tempx[j], tempy[j];
    
    char x[8] = "sob.txt";
    int N = no_of_trails;
    int D = m;
    P = sobol_points(N+1,D,x);
    
    temp = get_gaussian();
    gaussian_sum = sqrt(delta)*temp;
    S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
    S_t = S_1/m;
    S_k = S_1;
    S_t_hat_hat = pow(S_1,1.0/m);
    for (int k = 2; k <= m; k++){
        temp = get_gaussian();
        S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_t_hat_hat = S_t_hat_hat*pow(S_k, 1.0/m);
        S_t = S_t + S_k/m;
    }
    
    tempy[0] = max((S_t-K),0.0);
    tempx[0] = max((S_t_hat_hat-K),0.0);
    x_bar = tempx[0];
    y_bar = tempy[0];
    
    for(int i = 2; i<=j; i++){
        temp = get_gaussian();
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_t = S_1/m;
        S_t_hat_hat = pow(S_1,1.0/m);
        for (int k = 2; k <= m; k++){
            temp = get_gaussian();
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_t_hat_hat = S_t_hat_hat*pow(S_k, 1.0/m);
            S_t = S_t + S_k/m;
        }
        tempy[i-1] = max((S_t-K),0.0);
        tempx[i-1] = max((S_t_hat_hat-K),0.0);
        y_bar = (1.0 - 1.0 / i)*y_bar + tempy[i-1] / i;
        x_bar = (1.0 - 1.0 / i)*x_bar + tempx[i-1] / i;
    }
    
    double z_1,z_2,z_3;
    z_1 = z_2 = z_3 = 0;
    for(int i = 0; i<j;i++)
    {
        z_1 = z_1 + (tempx[i] - x_bar)*(tempy[i] - y_bar);
        z_2 = z_2 + (tempx[i] - x_bar)*(tempx[i] - x_bar);
        z_3 = z_3 + (tempy[i] - y_bar)*(tempy[i] - y_bar);
        
    }
    b = z_1/z_2;
    //cout<< "correlation = "<< z_1/sqrt(z_2*z_3) <<endl;
    //cout<< "b ="<<b<<endl;
    
    double E_X = option_price_call_black_scholes(S, K, r, q_hat, sqrt(v_hat_square),t_hat)*exp(r*t_hat);
    //cout<<"E_X ="<< E_X<<"!!!!!!!!!!!!!!"<<endl;
    
    double Y_bar;
    double Y_k;
    double x_k, y_k;
    
    random_shift(N, D);
    temp = get_gaussian_inverse_transform(P[1][0]);
    S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
    S_k = S_1;
    S_t = S_1/m;
    S_t_hat = pow(S_1,1.0/m);
    for (int k = 2; k <= m; k++){
        temp = get_gaussian_inverse_transform(P[1][k-1]);
        S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_t_hat = S_t_hat*pow(S_k, 1.0/m);
        S_t = S_t + S_k/m;
    }
    y_k = max((S_t-K),0.0);
    x_k = max((S_t_hat-K),0.0);
    Y_k = (y_k + b*(E_X - x_k));
    Y_bar = Y_k;
    for(int i = 2; i<=no_of_trails; i++){
        temp = get_gaussian_inverse_transform(P[i][0]);
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_t = S_1/m;
        S_t_hat = pow(S_1,1.0/m);
        for (int k = 2; k <= m; k++){
            temp = get_gaussian();
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_t_hat = S_t_hat*pow(S_k, 1.0/m);
            S_t = S_t + S_k/m;
        }
        y_k = max((S_t-K),0.0);
        x_k = max((S_t_hat-K),0.0);
        
        Y_k = (y_k + b*(E_X - x_k))*exp(-r*time);
        Y_bar = (1.0 - 1.0 / i)*Y_bar + Y_k / i;
    }
    X_BAR = Y_bar;
    Y_BAR = X_BAR*X_BAR;
    for(int p=1; p<L; p++){
        random_shift(N, D);
        temp = get_gaussian_inverse_transform(P[1][0]);
        S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
        S_k = S_1;
        S_t = S_1/m;
        S_t_hat = pow(S_1,1.0/m);
        for (int k = 2; k <= m; k++){
            temp = get_gaussian_inverse_transform(P[1][k-1]);
            S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_t_hat = S_t_hat*pow(S_k, 1.0/m);
            S_t = S_t + S_k/m;
        }
        y_k = max((S_t-K),0.0);
        x_k = max((S_t_hat-K),0.0);
        Y_k = (y_k + b*(E_X - x_k));
        Y_bar = Y_k;
        //y_bar = x_bar*x_bar;
        for(int i = 2; i<=no_of_trails; i++){
            temp = get_gaussian_inverse_transform(P[i][0]);
            S_1 = S*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
            S_k = S_1;
            S_t = S_1/m;
            S_t_hat = pow(S_1,1.0/m);
            for (int k = 2; k <= m; k++){
                temp = get_gaussian();
                S_k = S_k*exp(((r - q - 0.5*v*v)*time/m)+ sqrt(v*v*time/m)*temp);
                S_t_hat = S_t_hat*pow(S_k, 1.0/m);
                S_t = S_t + S_k/m;
            }
            y_k = max((S_t-K),0.0);
            x_k = max((S_t_hat-K),0.0);
            
            Y_k = (y_k + b*(E_X - x_k))*exp(-r*time);
            Y_bar = (1.0 - 1.0 / i)*Y_bar + Y_k / i;
            X_BAR = (1.0 - 1.0 / p)*X_BAR + Y_bar / p;
            Y_BAR = (1.0 - 1.0 / p)*Y_BAR + Y_bar*Y_bar / p;
        }
    }
    sample_mean = X_BAR;
    sample_mean_square = Y_BAR;
    return sample_mean;
}



int q1(int n, int m)
{
    
    no_of_trials = n;
    int sep = m;
    cout << "sample size is:" <<n<<endl;
    const clock_t begin_time = clock();
    call_price_MS = option_price_call_monte_carlo_simulaion(no_of_trials, initial_stock_price, strike_price, risk_free_rate, volatility, q, expiration_time,sep);
    cout << "Call Price according to Monte Carlo Simulaion = " << call_price_MS << endl;
    se = standard_error(no_of_trials);
    cout << "Estimate standard error is: " << se << endl;
    computational_time = float( clock () - begin_time ) /  CLOCKS_PER_SEC;
    cout << "computational time is "<< computational_time<<endl;
    efficiency = se*se*computational_time;
    cout << "computational efficiency is "<< efficiency<<endl;
    cout<<"-------------------------------------------"<<endl;
    return 0;
}

int q1_control(int n,int m)
{
    
    no_of_trials = n;
    cout << "sample size is:" <<n<<endl;
    const clock_t begin_time = clock();
    call_price_MS = control_variates(no_of_trials, initial_stock_price, strike_price, risk_free_rate, volatility, q, expiration_time,m);
    cout << "Call Price according to Monte Carlo Simulaion = " << call_price_MS << endl;
    se = standard_error(no_of_trials);
    cout << "Estimate standard error is: " << se << endl;
    computational_time = float( clock () - begin_time ) /  CLOCKS_PER_SEC;
    cout << "computational time is "<< computational_time<<endl;
    efficiency = se*se*computational_time;
    cout << "computational efficiency is "<< efficiency<<endl;
    cout<<"-------------------------------------------"<<endl;
    return 0;
}
int q2(int n,int m,int L)
{
    no_of_trials = n;
    cout << "sample size is:" <<n<<endl;
    const clock_t begin_time = clock();
    double call_price_MS = QMC_asian_call(initial_stock_price, strike_price, risk_free_rate, volatility, 0.0, expiration_time, m, n, L);
    cout << "Call Price according to Monte Carlo Simulaion = " << call_price_MS << endl;
    se = standard_error(L);
    cout << "Estimate standard error is: " << se << endl;
    computational_time = float( clock () - begin_time ) /  CLOCKS_PER_SEC;
    cout << "computational time is "<< computational_time<<endl;
    efficiency = se*se*computational_time;
    cout << "computational efficiency is "<< efficiency<<endl;
    cout<<"-------------------------------------------"<<endl;
    return 0;
}

int q2_control(int n,int m,int L)
{
    no_of_trials = n;
    cout << "sample size is:" <<n<<endl;
    const clock_t begin_time = clock();
    double call_price_MS = QMC_asian_call_Control(initial_stock_price, strike_price, risk_free_rate, volatility, 0.0, expiration_time, m, n, L);
    cout << "Call Price according to Monte Carlo Simulaion = " << call_price_MS << endl;
    se = standard_error(L);
    cout << "Estimate standard error is: " << se << endl;
    computational_time = float( clock () - begin_time ) /  CLOCKS_PER_SEC;
    cout << "computational time is "<< computational_time<<endl;
    efficiency = se*se*computational_time;
    cout << "computational efficiency is "<< efficiency<<endl;
    cout<<"-------------------------------------------"<<endl;
    return 0;
}

int q1_output_sample(){
    vector<int> num;
    for(int n = 10000; n <= 1000000; n+=10000)
        num.push_back(n);
    ofstream myfile2 ("q1_sample.txt");
    if (myfile2.is_open())
    {
        
        myfile2<<"\n";
        myfile2<<"sample_size, "<<"sample_mean, "<<"ci wide, "<<"se, "<<"computational_time, "<<"computational_efficiency, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q1(num[i],50);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        myfile2<<"\n";
        myfile2<<"sample_size, "<<"sample_mean, "<<"ci wide_control, "<<"se_control, "<<"computational_time, "<<"computational_efficiency_control, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q1_control(num[i],50);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        myfile2.close();
    }
    
    else
        cout << "Unable to open file";
    return 0;
}

int q2_output_sample(){
    vector<int> num;
    for(int n = 1000; n <= 100000; n+=1000)
        num.push_back(n);
    ofstream myfile2 ("q2_sample.txt");
    if (myfile2.is_open())
    {
        
        myfile2<<"\n";
        myfile2<<"sample_size, "<<"sample_mean, "<<"ci wide, "<<"se_control, "<<"computational_time, "<<"computational_efficiency, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q1_control(num[i],50);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        myfile2<<"\n";
        myfile2<<"sample_size, "<<"sample_mean, "<<"ci wide, "<<"se_qmc, "<<"computational_time, "<<"computational_efficiency, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q2(num[i]/30,50,30);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        myfile2<<"\n";
        myfile2<<"sample_size, "<<"sample_mean, "<<"ci wide, "<<"se_qmc_control, "<<"computational_time, "<<"computational_efficiency, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q2_control(num[i]/30,50,30);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        
        myfile2.close();
    }
    
    else
        cout << "Unable to open file";
    return 0;
}

int q3_output_sample(){
    vector<int> num;
    for(int n = 3000; n <= 300000; n+=3000)
        num.push_back(n);
    ofstream myfile2 ("q3_sample.txt");
    if (myfile2.is_open())
    {
        
        
        myfile2<<"\n";
        myfile2<<"m, "<<"sample_mean, "<<"ci wide, "<<"se_control, "<<"computational_time, "<<"computational_efficiency, "<<"sample_mean_qmc, "<<"ci wide_qmc, "<<"se_qmc, "<<"computational_time_qmc, "<<"computational_efficiency_qmc, "<<"sample mean_qmc_control, "<<"ci wide_qmc_control, "<<"se_qmc_control, "<<"computational_time_qmc_control, "<<"computational_efficiency_qmc_control, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q1_control(num[i],200);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<",";
            q2(num[i]/30,200,30);
            ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<",";
            q2_control(num[i]/30,200,30);
            ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        myfile2.close();
    }
    
    else
        cout << "Unable to open file";
    return 0;
}

int q3_output_m(){
    vector<int> num;
    for(int n = 50; n <= 1000; n+=50)
        num.push_back(n);
    ofstream myfile2 ("m.txt");
    if (myfile2.is_open())
    {
        
        
        myfile2<<"\n";
        myfile2<<"m, "<<"sample_mean, "<<"ci wide, "<<"se_control, "<<"computational_time, "<<"computational_efficiency, "<<"sample_mean_qmc, "<<"ci wide_qmc, "<<"se_qmc, "<<"computational_time_qmc, "<<"computational_efficiency_qmc, "<<"sample mean_qmc_control, "<<"ci wide_qmc_control, "<<"se_qmc_control, "<<"computational_time_qmc_control, "<<"computational_efficiency_qmc_control, "<<"\n";
        for(int i =0; i<num.size(); i++)
        {
            q1_control(3000,num[i]);
            double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<num[i]<<", "<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<",";
            q2(1000,num[i],30);
            ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<",";
            q2_control(1000,num[i],30);
            ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
            myfile2<<sample_mean<<", "<<ci_wide<<", "<<se<<", "<<computational_time<<", "<<efficiency<<"\n";
            
        }
        
        myfile2.close();
    }
    
    else
        cout << "Unable to open file";
    return 0;
}


int main(int argc, char* argv[])
{
    x10 = rand() % (m1-1);
    x11 = rand() % (m1-1);
    x12 = rand() % (m1-1);
    x20 = rand() % (m2-1);
    x21 = rand() % (m2-1);
    x22 = rand() % (m2-1);
    
    expiration_time = 1;
    risk_free_rate = 0.1;
    volatility = 0.2;
    q = 0.00;
    initial_stock_price=100;
    strike_price = 100;
    monitor = 50;
    
    expiration_time = 2;
    risk_free_rate = 0.05;
    volatility = 0.5;
    initial_stock_price = 2;
    strike_price = 2;
    q3_output_sample();
    //q2_control(20000,200,30);
    double ci_wide =  (sample_mean + 1.96*se) - (sample_mean - 1.96*se);
    cout<<"["<<(sample_mean - 1.96*se)<<", "<<(sample_mean + 1.96*se)<<"];<<ci_wide:"<<ci_wide<<endl;
    


    
    
    
}

