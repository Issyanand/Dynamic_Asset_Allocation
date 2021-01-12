library("SMFI5")



######################################################################################################################

########################## Downloading Prices
require(tidyquant)
options("getSymbols.warning4.0"=FALSE)
options("getSymbols.yahoo.warning"=FALSE)
tickers <- c("AAPL","GS","UL","PFE","GOOG","KO","BAC", "JNJ","PG","NKE")
getSymbols(tickers, from = '2004-08-19',to = "2020-10-28")
prices <- map(tickers,function(x) Ad(get(x)))
prices <- reduce(prices,merge) ; colnames(prices) <- tickers

########################## risk free from fama french
require(tidyverse)
ff_url <- "https://mba.tuck.dartmouth.edu/pages/faculty/ken.french/ftp/F-F_Research_Data_Factors_daily_CSV.zip"
temp_file <- tempfile() ; download.file(ff_url, temp_file)
ff_factors_raw_data <- unzip(temp_file)
ff_factors_raw_data <- as.matrix(read_csv(ff_factors_raw_data, skip = 3))
rf<-as.vector(ff_factors_raw_data[ff_factors_raw_data[,1]>20040819&ff_factors_raw_data[,1]<20201028,][,5])
rf_vec <- rf[1:(length(rf)-1)]
rf <- mean(rf_vec) # mean of risk free
########################## including risk free with the assets
A <- 3 #risk aversion
mu_max <- 0.1
points_front <- 100
prices <- as.matrix(prices)
rets <- ((prices[2:nrow(prices),]/prices[1:(nrow(prices)-1),]) -1)
mu <- apply(rets,2,mean)*252 # mean of returns 
cov_mat <- as.matrix(cov(rets))*252 # covarince matrix
#####running change of allocation over time period - "years"
years <- 50
weights <- matrix(0,years,3)
# loop to get weights over time (uncomment below and change line 41 to run weights)
#for(k in 1:years){
######### Calling rf, theta and spd ######################################################      
# calling
N <- 10000 #number of simulated trajectories
TT <- 1 #time horizon (change it to k if you are running a looop to get weights over time)
M <- TT*252 #number of steps 
dt <- 1/252 #each step

# give values for theta 
port_market_mean <- apply(rets,1,mean) * 252  # market porfolio mean
port_market_stdev <- stdev(port_market_mean) * sqrt(252) # market portfolio stdev
theta <- (port_market_mean - rf)/port_market_stdev # with historical rf values; port_market_mean is the return of are equally weighted portfolio and port_market_stdev is the stdev of equi weighted market portfolio
theta_bar <- mean(theta)  # mean of theta to use for simulation
sigma_theta <- stdev(theta)
k_theta <- log(var(theta)/cov(rf_vec[2:length(theta)],rf_vec[1:(length(theta)-1)]))
# giving values for rf
sigma_r <- sd(rf_vec)
r_bar <- mean(rf_vec)
k_rf <- as.numeric(est.ou(rf_vec)[["param.exp"]][1])



################################# State Price Density Function ##################################

simulate_spd <- function(rf_sim,theta_sim,TT,M,dt,N){
  spd_results <- matrix(0,M,N)
  spd_results[1,] <- 1
  for(i in 2:M){
    dw <- rnorm(N)*dt
    spd_results[i,] <- spd_results[i-1,] - spd_results[i-1,]*(rf_sim[i-1]*dt + theta_sim[i-1]*dw)
  }
  return(apply(spd_results,1,mean))
}

###################################Calling the functions###################################################################################
rf_sim <- sim.vasicek(k_rf,r_bar,sigma_r,r_bar,M,dt)
theta_sim <- sim.vasicek(k_theta,theta_bar,sigma_theta,theta_bar,M,dt)
spd_sim<- simulate_spd(rf_sim,theta_sim,TT,M,dt,N)
###################################Hedging portfolios###################################################################################
Hedge_rf <- -(sigma_r/k_rf)*exp(-k_rf*TT) + (sigma_r/k_rf)
Hedge_market1 <- 0
Hedge_market2 <- 0
for (i in 1:M){
  dw <- rnorm(N)*dt
  Hedge_market1 <- Hedge_market1 + sigma_theta*(theta_sim[i]*exp(-k_theta*i)*dt) 
  Hedge_market2 <- Hedge_market2 + mean(sigma_theta*exp(-k_theta*i)*dw)
}
Hedge_market <- Hedge_market1 + Hedge_market2

######################################################################################################################

# more inputs required 
W = 100000000 # intial wealth

# function returning the mean variance portfolio

frontier <- function(rf,cov_mat,mu,A,mu_max,points_front,spd_sim,W,Hedge_rf,Hedge_market){
  
  length <- nrow(cov_mat)  # no. of observations
  one_vec <- as.vector(matrix(1,1,length)) # vector of ones
  cov_inv <- solve(cov_mat) # inverse of the covariance matrix
  
  
  #1) Minimum Variance Portfolio
  
  mv_port <- (cov_inv%*%one_vec)/as.numeric(t(one_vec)%*%cov_inv%*%one_vec)  # weights of minimum variance port
  sum(mv_port)
  mu_mv <- t(mv_port)%*%as.vector(mu) # mean of minimum variance port
  sigma_mv <- sqrt(t(mv_port)%*%cov_mat%*%mv_port) # standard deviation of minimum variance
  
  ########## excess returns with or without risk free 
  
  mu_excess_norf <- mu - one_vec%*%mu_mv
  mu_excess_rf <- mu - one_vec%*%as.matrix(rf)
  
  #2) Mean-Variance Portfolio without risk free
  
  m_port_norf <- cov_inv%*%mu_excess_norf # weights of Mean-Variance port
  sum(m_port_norf)
  mu_m_norf <- t(m_port_norf)%*%as.vector(mu)  # mean of Mean-Variance port
  sigma_m_norf <- sqrt(t(m_port_norf )%*%cov_mat%*%m_port_norf ) # standard deviation of Mean-Variance
  
  #3) Optimal portfolio without riskfree asset
  
  opt_port_norf <- mv_port + m_port_norf/A # weights of Optimal portfolio
  sum(opt_port_norf)
  mu_opt_norf <- t(opt_port_norf)%*%as.vector(mu)  # mean of Optimal portfolio
  sd_opt_norf <- sqrt(t(opt_port_norf )%*%cov_mat%*%opt_port_norf ) # standard deviation of Optimal portfolio
  
  #4) Mean-variance portfolio with riskfree asset
  
  m_port_rf <- cov_inv%*%mu_excess_rf # weights of Mean-Variance port
  sum(m_port_rf)
  # Expected return and volatility of portfolio with riskfreeasset
  mu_m_rf <- t(m_port_rf)%*%as.vector(mu) + (1- t(m_port_rf)%*%one_vec)*rf;
  sigma_m_rf <- sqrt(t(m_port_rf)%*%cov_mat%*%m_port_rf);
  
  
  #5) Optimal portfolio with riskfree asset 
  opt_port_rf <-  m_port_rf/A;  # weights of Optimal portfolio
  sum(opt_port_rf)
  # Expected return and volatility of portfolio with riskfreeasset
  mu_opt_port_rf <- t(opt_port_rf)%*%as.vector(mu)+(1-t(opt_port_rf)%*%one_vec)*rf;
  sigma_opt_port_rf <- sqrt(t(opt_port_rf)%*%cov_mat%*%opt_port_rf);
  
  #6) Tangency portfolio ##########################
  
  port_tangency = m_port_rf/as.numeric((t(one_vec)%*%m_port_rf));
  
  mu_tangency = t(port_tangency)%*%mu ; # expected return of tangency portfolio
  sigma_tangency =sqrt(t(port_tangency)%*%cov_mat%*%port_tangency); # volatility of tangency portfolio
  
  
  #7) Hedging portfolio ###################################### 
  m_port_hedging <- (spd_sim[1]*(W/A)*(cov_inv%*%mu_excess_rf))/W
  m_port_hedging_rf <- (-(1/sqrt((diag(cov_mat))))*spd_sim[1]*W*(1-(1/A))*Hedge_rf)/W
  m_port_hedging_market<- (-(1/sqrt((diag(cov_mat))))*spd_sim[1]*W*(1-(1/A))*Hedge_market)/W
  port_hedging <- (m_port_hedging + m_port_hedging_rf +m_port_hedging_market)
  mu_hedge <- t(port_hedging)%*%mu
  sigma_hedge <- sqrt(t(port_hedging)%*%(cov_mat%*%port_hedging))
  port_hedging_norm <- port_hedging/sum(port_hedging)
  mu_hedge_norm <- t(port_hedging_norm)%*%mu
  sigma_hedge_norm <- sqrt(t(port_hedging_norm)%*%(cov_mat%*%port_hedging_norm))
  ########################## Frontier portfolios ##########################
  
  # Vector of target expected returns
  mu_graph_max <- max(mu_max,mu_m_rf,mu_opt_port_rf,mu_hedge);
  mu_target_vec <- seq(0,mu_graph_max,length.out = points_front)
  
  # Initialize frontier portfolio vectors and its moments
  port_front <- matrix(0,length,points_front);
  mu_front <- matrix(0,points_front,1);
  sigma_front <- matrix(0,points_front,1); 
  port_front_target <- 0
  #Calculate frontier portfolios for target expected returns and
  #correspoinding expected returns and volatilities
  for(j in 1:points_front){
    port_front_target <- mv_port + as.vector(as.numeric(as.numeric(mu_target_vec[j]-mu_mv)/as.numeric(t(mu_excess_norf)%*%(cov_inv%*%mu_excess_norf)))%*%as.numeric(m_port_norf));
    port_front[,j] = port_front_target;
    mu_front[j,]=t(port_front_target)%*%mu;
    sigma_front[j,]=sqrt(t(port_front_target)%*%cov_mat%*%(port_front_target))
    
  }
  
  ########################## Frontier portfolios ends ##########################
  #Sharpe ratio of tangency and optimal portfolio
  #SR_tangency=(mu_tangency-r)./sigma_tangency; %note that optimal
  #portfolio and tangency portfolio have same Sharpe ratio but weights of
  #tangency portfolio sum to one
  SR_m_port_rf=(mu_m_rf-rf)/sigma_m_rf;
  
  ########################## Vector of target for Captial market line 
  sigma_vec=seq(0,max(sigma_front,sigma_m_rf,sigma_m_norf),length.out = points_front);
  ########################## Captial market line
  mu_front_rf = rf + SR_m_port_rf%*%sigma_vec;
  
  
  
  ########################## plots ########################## 
  plot(sigma_front,mu_front,type ='l', xlim = c(0,max(sigma_vec)),ylim = c(0,mu_graph_max),xlab = "stdev",ylab = "mu") # plotting the efficient frontier
  points(sqrt(diag(cov_mat)),mu,pch=20) # all the securities
  points(sigma_mv,mu_mv,col="dark green") # minimum variance
  points(sigma_hedge,mu_hedge, col = "purple")
  points(sigma_hedge_norm,mu_hedge_norm, col = "red")
  points(sigma_tangency,mu_tangency,col="blue") # tangency portfolio
  points(sigma_opt_port_rf,mu_opt_port_rf,col = "green") # optimal portfolio with rf
  par(new=TRUE)
  plot(sigma_vec, mu_front_rf,type = "l",xlim = c(0,max(sigma_vec)),ylim = c(0,mu_graph_max),xlab = "stdev",ylab = "mu",col = "grey" )
  
  legend("bottomright", legend=c("Minimum Variance Portfolio", "Tangency Portfolio","Optimal Portfolio","Dynamic Hedge Portfolio","Dynamic Hedge Portfolio Normalized"),col=c("dark green", "blue","Green","purple","red"),pch=1, cex=0.5)
  legend("topleft", legend=c("securities"),pch=20, cex=0.5)
  
  mean_variance_hedge_percent <- 100*sum(m_port_hedging) / sum(port_hedging)
  m_port_hedging_rf_percent <- 100* sum(m_port_hedging_rf) / sum(port_hedging)
  m_port_hedging_market_percent <- 100* sum(m_port_hedging_market) / sum(port_hedging)
  weigths_dist <- c(mean_variance_hedge_percent,m_port_hedging_rf_percent,m_port_hedging_market_percent)
  return(matrix(weigths_dist))
  
} 

#Frontier function ends

frontier(rf,cov_mat,mu,A,mu_max,points_front,spd_sim,W,Hedge_rf,Hedge_market)

              

            
# Uncomment all to run weights over time            
#weights[k,] <- frontier(rf,cov_mat,mu,A,mu_max,points_front,spd_sim,W,Hedge_rf,Hedge_market)
#}

# calling porfolio weight distribution over time horizon
#weights 
#mv <- weights[,1]
#hedge_rf <- weights[,2]
#hedge_market <- weights[,3]
#plot(mv,type='l',ylim=c(-100,200),ylab = "Percentage weight assigned",xlab="years",col="red")
#par(new=TRUE)
#plot(hedge_rf,type='l',ylim=c(-100,200),ylab = "Percentage weight assigned",xlab="years",col="blue")
#par(new=TRUE)
#plot(hedge_market,type='l',ylim=c(-100,200),ylab = "Percentage weight assigned",xlab="years",col="green")
legend("bottomright", legend=c("Mean Varinace Portfolio","Risk free Hedge Portfolio","Market Hedge Portfolio"),col =c("Red","blue","green") ,lty=1, cex=0.3)
