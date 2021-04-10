# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#       A Rao-Yu model for small area estimation based      # # # # # # # # # # # # # # # # # # # # # #
# on uncertain data obtained from dependent survey estimates# # # # # # # # # # # # # # # # # # # # # #
#                   - Example Code -                        # # # # # # # # # # # # # # # # # # # # # #
#    Jan Pablo Burgard, Joscha Krause, Domingo Morales      # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


# ---- Packages ----
library(mvtnorm) # for bootstrapping
library(nloptr)  # for maximum likelihood estimation


# ---- Load Data ----
# Insert the path to the file "MERY_Example.RData" on your pc
# path <- " " 
# load(paste(path, "MERY_Example.RData", sep=""))

# Main data frame
Data <- ExampleData$Data 
# Domain:     domain index
# Period:     period index
# Y.direct:   direct estimator of the target variable
# Var.direct: variance of Y.direct
# X1.direct:  direct estimator of the first covariate
# X2.direct:  direct estimator of the second covariate

# List of error variance-covariance matrices (Y- and X-errors)
Cov.error <- ExampleData$Cov.error

# List of error covariances (Y- and X-errors)
Cov.ev <- ExampleData$Cov.ev

# List of covariate error variance-covariance matrices (X-errors)
Cov.v <- ExampleData$Cov.v


# ---- Model parameter estimation ----
# theta:   vector of model parameter estimates
# y:       vector of direct target variable estimates
# x:       matrix of direct covariate estimates
# D:       number of domains
# p:       number of covariates
# area:    index of area affiliation
# subarea: index of subarea affiliation
# sigma.e: vector of target variable sampling variances (Y-errors)
# sigma.v: list of covariate error variance-covariance matrices (X-errors)
# cov.ev:  list of error variance-covariance matrices (Y- and X-errors)
# method:  fitting algorithm (ML, REML)
# eps:     tolerance for convergence for model parameter estimation

# Computes the value of the loglikehood function for a domain
area.loglik <- function(theta, y, x, D, time, sigma.e, sigma.v, cov.ev, p){
  b0       <- theta[1]
  b        <- theta[2:(p+1)]
  sigma.u1 <- theta[p+2]
  sigma.u2 <- theta[p+3]
  I        <- matrix(1, time, time)
  v.comp1  <- rep(NA, time)
  v.comp2  <- rep(NA, time)
  v.comp3  <- rep(NA, time)
  for(t in 1:time){
    sigma.vt   <- sigma.v[[t]]
    cov.vt     <- cov.ev[[t]]
    v.comp1[t] <- c(t(b)%*%sigma.vt%*%b)
    v.comp2[t] <- c(2*t(b)%*%cov.vt)
    v.comp3[t] <- sigma.u2+sigma.e[t]
  }
  H     <- diag(v.comp1+v.comp2+v.comp3)
  H.inv <- solve(H)
  V     <- sigma.u1*I+H
  V.inv <- solve(V)
  comp1 <- c(determinant(V)$modulus)
  z     <- cbind(1,x)
  b     <- c(b0,b)
  comp2 <- c(t(y-z%*%b)%*%V.inv%*%(y-z%*%b))
  res   <- c(comp1, comp2)
  res
}
# Computes the value of the negative loglikelihood over all domains
loglik <- function(theta, y, x, D, time, sigma.e, sigma.v, cov.ev, p){
  comp1 <- ((D*time)/2)*log(2*pi)
  comp2 <- matrix(NA, ncol=2, nrow=D)
  for(d in 1:D){
    y.d       <- y[which(area==d)]
    x.d       <- x[which(area==d),]
    sigma.e.d <- sigma.e[which(area==d)]
    sigma.v.d <- sigma.v[which(area==d)]
    cov.ev.d  <- cov.ev[which(area==d)]
    comp2[d,]  <- area.loglik(theta=theta, y=y.d, x=x.d, D=D, time=time, p=p,
                              sigma.e=sigma.e.d, sigma.v=sigma.v.d, cov.ev=cov.ev.d)
  }
  res <- -comp1-0.5*sum(comp2[,1])-0.5*sum(comp2[,2])
  -res
}
# Computes the value of the gradient of the loglikelihood function for a domain
area.grad <- function(theta, y, x, D, time, sigma.e, sigma.v, cov.ev, p){
  b0       <- theta[1]
  b        <- theta[2:(p+1)]
  sigma.u1 <- theta[p+2]
  sigma.u2 <- theta[p+3]
  I        <- matrix(1, time, time)
  v.comp1  <- rep(NA, time)
  v.comp2  <- rep(NA, time)
  v.comp3  <- rep(NA, time)
  for(t in 1:time){
    sigma.vt   <- sigma.v[[t]]
    cov.vt     <- cov.ev[[t]]
    v.comp1[t] <- c(t(b)%*%sigma.vt%*%b)
    v.comp2[t] <- c(2*t(b)%*%cov.vt)
    v.comp3[t] <- sigma.u2+sigma.e[t]
  }
  H       <- diag(v.comp1+v.comp2+v.comp3)
  H.inv   <- solve(H)
  V       <- sigma.u1*I+H
  V.inv   <- solve(V)
  delta   <- t(t(c(1,rep(0,p))))
  z       <- cbind(1,x)
  grad.1  <- c(t(delta)%*%t(z)%*%V.inv%*%(y-z%*%c(b0,b)))
  grad.21 <- rep(NA,p)
  grad.22 <- rep(NA,p)
  grad.23 <- rep(NA,p)
  for(k in 1:p){
    delta.k    <- rep(0,p)
    delta.k[k] <- 1
    b.comp     <- rep(NA, time)    
    for(t in 1:time){
      sigma.vt   <- sigma.v[[t]]
      cov.vt     <- cov.ev[[t]]
      b.comp[t]  <- 2*c(t(delta.k)%*%sigma.vt%*%b+t(delta.k)%*%cov.vt)
    }
    VderivB    <- diag(b.comp)
    grad.21[k] <- sum(diag(V.inv%*%VderivB))
    grad.22[k] <- c(t(y-z%*%c(b0,b))%*%V.inv%*%VderivB%*%V.inv%*%(y-z%*%c(b0,b)))
    grad.23[k] <- c(t(delta.k)%*%t(x)%*%V.inv%*%(y-z%*%c(b0,b)))
  }
  grad.2     <- rbind(grad.21, grad.22, grad.23)
  Vdsigma.1  <- matrix(1, time, time)
  Vdsigma.2  <- diag(rep(1, time))
  grad.31    <- sum(diag(V.inv%*%Vdsigma.1))
  grad.32    <- c(t(y-z%*%c(b0,b))%*%V.inv%*%Vdsigma.1%*%V.inv%*%(y-z%*%c(b0,b)))
  grad.41    <- sum(diag(V.inv%*%Vdsigma.2))
  grad.42    <- c(t(y-z%*%c(b0,b))%*%V.inv%*%Vdsigma.2%*%V.inv%*%(y-z%*%c(b0,b)))
  grad.3     <- rbind(c(grad.31, grad.32), c(grad.41, grad.42))
  val        <- list(grad.1, grad.2, grad.3)
  val
}
# Computes the value of the gradient of the negative loglikelihood function over all domains
grad <- function(theta, y, x, D, time, sigma.e, sigma.v, cov.ev, p){
  grad.mat <- matrix(NA, ncol=p+3, nrow=D)
  for(d in 1:D){
    y.d       <- y[which(area==d)]
    x.d       <- x[which(area==d),]
    sigma.e.d <- sigma.e[which(area==d)]
    sigma.v.d <- sigma.v[which(area==d)]
    cov.ev.d  <- cov.ev[which(area==d)]
    grad.obj  <- area.grad(theta=theta, y=y.d, x=x.d, D=D, time=time, p=p,
                           sigma.e=sigma.e.d, sigma.v=sigma.v.d, cov.ev=cov.ev.d)
    grad.mat[d,1]       <- grad.obj[[1]]
    b.mat               <- grad.obj[[2]]
    for(k in 1:p){
      b.val           <- -0.5*b.mat[1,k]+0.5*b.mat[2,k]+b.mat[3,k]
      grad.mat[d,k+1] <- b.val
    }
    sigma.mat       <- grad.obj[[3]]
    grad.mat[d,k+2] <- -0.5*sigma.mat[1,1]+0.5*sigma.mat[1,2]
    grad.mat[d,k+3] <- -0.5*sigma.mat[2,1]+0.5*sigma.mat[2,2]
  } 
  grad.val <- colSums(grad.mat)
  -grad.val
}
# Estimates the model parameters of the MERY model via the maximum likelihood method
MERY <- function(y, x, area, theta.init, D, time, sigma.e, sigma.v, cov.ev, method="NR", p, eps=1e-4){
  if(method=="NR"){
    opt.mod <- nloptr(x0=theta.init, eval_f=loglik, eval_grad_f=grad, y=y, x=x,
                      D=D, time=time, sigma.e=sigma.e, sigma.v=sigma.v,
                      cov.ev=cov.ev, p=p, lb=c(rep(-10^4,p+1),0,0),
                      opts=list("algorithm"="NLOPT_LD_SLSQP", 
                                "xtol_rel"=eps)) 
  }else{
    opt.mod <- nloptr(x0=theta.init, eval_f=loglik, y=y, x=x,
                      D=D, time=time, sigma.e=sigma.e, sigma.v=sigma.v,
                      cov.ev=cov.ev, p=p,
                      opts=list("algorithm"="NLOPT_LN_NELDERMEAD", 
                                "xtol_rel"=eps))
  }
  result <- opt.mod$solution
  result[(p+2):(p+3)] <- sqrt(result[(p+2):(p+3)])
  result
}

# Application
D     <- length(unique(Data$Domain)) # Number of domains
Time  <- length(unique(Data$Period)) # Number of periods
p     <- 2 # Number of covariates / slope parameters
y     <- Data$Y.direct # Direct estimators of the target variable
X     <- as.matrix(Data[,c("X1.direct", "X2.direct")]) # Direct estimators of the covariates
area  <- Data$Domain # Domain index
sigma.e    <- Data$Var.direct # Variance of target variable direct estimator
theta.init <- c(10, 2, 2, 10, 5) # Initial model parameter estimates (e.g. from the Rao-Yu model)
theta.est  <- MERY(y=y, x=X, area=area, D=D, time=Time, theta.init=theta.init, sigma.e=sigma.e,
                   sigma.v=Cov.v, cov.ev=Cov.ev, p=p)
theta.est # MERY model parameter estimates


# ---- Prediction ----
# Computes the BP / EBP under the MERY model
predictMERY <- function(y, x, area, theta, p, D, time,  sigma.e, sigma.v, cov.ev){
  beta.0    <- theta[1]
  beta.1    <- theta[2:(p+1)]
  b         <- theta[1:(p+1)]
  sigma.1   <- theta[p+2]
  sigma.2   <- theta[p+3]
  mu.BP     <- list()
  for(d in 1:D){
    sigma.e.d <- sigma.e[which(area==d)]
    sigma.v.d <- sigma.v[which(area==d)]
    cov.ev.d  <- cov.ev[which(area==d)]
    y.d       <- y[which(area==d)]
    X.d       <- x[which(area==d),]
    Z.d       <- cbind(1, X.d)
    B.d       <- matrix(0, ncol=time*p, nrow=time)
    I.T       <- matrix(1, ncol=time, nrow=time)
    I.T2      <- diag(rep(1,time))
    i.T       <- matrix(1, nrow=time, ncol=1)
    C.d       <- matrix(0, ncol=time*p, nrow=time)
    S.yv.d    <- matrix(0, ncol=time, nrow=time)
    S.yu2.d   <- matrix(0, ncol=time, nrow=time)
    S.v.d     <- matrix(0, ncol=time*p, nrow=time*p)
    a.d       <- rep(NA, time)
    for(t in 1:time){
      B.d[t,((t-1)*p+1):(t*p)] <- beta.1
      sigma.e.dt <- sigma.e.d[[t]]
      sigma.v.dt <- sigma.v.d[[t]]
      cov.ev.dt  <- cov.ev.d[[t]]
      a.dt       <- 1/(t(beta.1)%*%sigma.v.dt%*%beta.1+2*t(beta.1)%*%cov.ev.dt+sigma.2+sigma.e.dt)
      a.d[t]     <- a.dt
      c.dt       <- t(cov.ev.dt)%*%solve(sigma.v.dt)
      c2.dt      <- sigma.2+sigma.e.dt-(c.dt%*%cov.ev.dt)
      c3.dt      <- t(beta.1)%*%sigma.v.dt%*%beta.1+2*t(beta.1)%*%cov.ev.dt+sigma.e.dt
      C.d[t,c(((t-1)*p)+1, t*p)] <- c.dt
      diag(S.yv.d)[t]  <- c2.dt
      diag(S.yu2.d)[t] <- c3.dt
      S.v.d[c(((t-1)*p+1):(t*p)), c(((t-1)*p+1):(t*p))] <- sigma.v.dt
    }
    a.dt       <- 1/sigma.1+sum(a.d)
    C.d        <- B.d+C.d
    S.yv.d     <- sigma.1*I.T+S.yv.d
    S.yu2.d    <- sigma.1*I.T+S.yu2.d
    BP.v.d     <- solve(solve(S.v.d)+t(C.d)%*%solve(S.yv.d)%*%C.d)%*%t(C.d)%*%solve(S.yv.d)%*%(y.d-Z.d%*%b)
    BP.u2.d    <- solve(solve(S.yu2.d)+I.T2)%*%solve(S.yu2.d)%*%(y.d-Z.d%*%b)
    BP.u1.d    <- (1/a.dt)*t(a.d)%*%(y.d-Z.d%*%b)
    mu.BP[[d]] <- Z.d%*%b+B.d%*%BP.v.d+i.T%*%BP.u1.d+BP.u2.d
  }
  mu.BP <- c(do.call(rbind.data.frame, mu.BP))
  unlist(mu.BP)
}

# Application
pred <- predictMERY(y=y, x=X, area=area, D=D, time=Time, theta=theta.est, sigma.e=sigma.e,
                    sigma.v=Cov.v, cov.ev=Cov.ev, p=p)
pred # MERY domain characteristic predictions


# ---- MSE estimation ----
# Computes a plug-in estimator for the MSE of the EBP
CMSE.MERY <- function(y, x, area, theta, D, time,  sigma.e, sigma.v, cov.ev, type){
  beta.0  <- theta[1]
  beta.1  <- theta[2:(p+1)]
  b       <- theta[1:(p+1)]
  sigma.1 <- theta[p+2]
  sigma.2 <- theta[p+3]
  if(type=="vector"){
    cmse <- rep(NA, D*time)  
  }
  if(type=="matrix"){
    CMSE.mat <- list()
  }
  if(type=="components"){
    S.1.mat   <- list()
    S.2.mat   <- list()
    S.3.mat   <- list() 
  }
  if(type=="detailed"){
    S.1.1.mat <- list()
    S.1.2.mat <- list()
    S.1.3.mat <- list()
    S.1.4.mat <- list()
    S.1.5.mat <- list()
    S.1.6.mat <- list()
    S.1.7.mat <- list()
    S.1.8.mat <- list()
    S.1.9.mat <- list()
    S.1.0.mat <- list()
    S.2.1.mat <- list()
    S.2.2.mat <- list()
    S.2.3.mat <- list()
    S.2.4.mat <- list()
    S.3.1.mat <- list()
    S.3.2.mat <- list()
    S.3.3.mat <- list()
    S.3.4.mat <- list()
    S.3.5.mat <- list()
    S.3.6.mat <- list()
    S.3.7.mat <- list()
    S.3.8.mat <- list()
    S.3.9.mat <- list()
    S.3.0.mat <- list()
  }
  for(d in 1:D){
    sigma.e.d <- sigma.e[which(area==d)]
    sigma.v.d <- sigma.v[which(area==d)]
    cov.ev.d  <- cov.ev[which(area==d)]
    y.d       <- y[which(area==d)]
    X.d       <- x[which(area==d),]
    Z.d       <- cbind(1, X.d)
    B.d       <- matrix(0, ncol=time*p, nrow=time)
    I.T       <- matrix(1, ncol=time, nrow=time)    
    i.T       <- matrix(1, nrow=time, ncol=1)       
    I.T2      <- diag(rep(1,time))                 
    C.d       <- matrix(0, ncol=time*p, nrow=time)
    Cov.d     <- matrix(0, ncol=time, nrow=time*p)
    S.yv.d    <- matrix(0, ncol=time, nrow=time)    
    S.yu2.d   <- matrix(0, ncol=time, nrow=time)    
    S.v.d     <- matrix(0, ncol=time*p, nrow=time*p)
    v.comp1   <- rep(NA, time)
    v.comp2   <- rep(NA, time)
    v.comp3   <- rep(NA, time)
    a.d       <- rep(NA, time)
    for(t in 1:time){
      B.d[t,((t-1)*p+1):(t*p)] <- beta.1
      sigma.e.dt <- sigma.e.d[[t]]
      sigma.v.dt <- sigma.v.d[[t]]
      cov.ev.dt  <- cov.ev.d[[t]]
      a.dt       <- 1/(t(beta.1)%*%sigma.v.dt%*%beta.1+2*t(beta.1)%*%cov.ev.dt+sigma.2+sigma.e.dt)
      a.d[t]     <- a.dt
      Cov.d[((t-1)*p+1):(t*p),t] <- cov.ev.dt
      c.dt       <- t(cov.ev.dt)%*%solve(sigma.v.dt)
      c2.dt      <- sigma.2+sigma.e.dt-(c.dt%*%cov.ev.dt)
      c3.dt      <- t(beta.1)%*%sigma.v.dt%*%beta.1+2*t(beta.1)%*%cov.ev.dt+sigma.e.dt
      C.d[t,c(((t-1)*p)+1, t*p)] <- c.dt
      diag(S.yv.d)[t]  <- c2.dt
      diag(S.yu2.d)[t] <- c3.dt
      S.v.d[c(((t-1)*p+1):(t*p)), c(((t-1)*p+1):(t*p))] <- sigma.v.dt
      v.comp1[t] <- c(t(beta.1)%*%sigma.v.dt%*%beta.1)
      v.comp2[t] <- c(2*t(beta.1)%*%cov.ev.dt)
      v.comp3[t] <- sigma.2+sigma.e.dt
    }
    H        <- diag(v.comp1+v.comp2+v.comp3)
    V.d      <- sigma.1*I.T+H
    a.dt     <- 1/sigma.1+sum(a.d)
    C.d      <- B.d+C.d
    S.yv.d   <- sigma.1*I.T+S.yv.d
    S.yu2.d  <- sigma.1*I.T+S.yu2.d
    Svd.inv  <- solve(S.v.d)
    Syvd.inv <- solve(S.yv.d)
    Syu2.inv <- solve(S.yu2.d)
    s.comp.1 <- solve(Svd.inv+t(C.d)%*%Syvd.inv%*%C.d)
    s.comp.2 <- solve(I.T2+Syu2.inv)
    s.comp.3 <- Z.d%*%b%*%t(b)%*%t(Z.d)
    S.1.1 <- s.comp.3
    S.1.2 <- B.d%*%s.comp.1%*%t(C.d)%*%Syvd.inv%*%V.d%*%Syvd.inv%*%C.d%*%s.comp.1%*%t(B.d)
    S.1.3 <- B.d%*%s.comp.1%*%t(C.d)%*%Syvd.inv%*%V.d%*%a.d%*%(1/a.dt)%*%t(i.T)
    S.1.4 <- B.d%*%s.comp.1%*%t(C.d)%*%Syvd.inv%*%V.d%*%Syu2.inv%*%s.comp.2
    S.1.5 <- i.T%*%(1/a.dt)%*%t(a.d)%*%V.d%*%Syvd.inv%*%C.d%*%s.comp.1%*%t(B.d)
    S.1.6 <- i.T%*%(1/(a.dt^2))%*%t(a.d)%*%V.d%*%a.d%*%t(i.T)
    S.1.7 <- i.T%*%(1/a.dt)%*%t(a.d)%*%V.d%*%Syu2.inv%*%s.comp.2
    S.1.8 <- s.comp.2%*%Syu2.inv%*%V.d%*%Syvd.inv%*%C.d%*%s.comp.1%*%t(B.d)
    S.1.9 <- s.comp.2%*%Syu2.inv%*%V.d%*%a.d%*%(1/a.dt)%*%t(i.T)
    S.1.0 <- s.comp.2%*%Syu2.inv%*%V.d%*%Syu2.inv%*%s.comp.2
    S.1   <- S.1.1+S.1.2+S.1.3+S.1.4+S.1.5+S.1.6+S.1.7+S.1.8+S.1.9+S.1.0
    S.2.1 <- s.comp.3
    S.2.2 <- B.d%*%S.v.d%*%t(B.d)
    S.2.3 <- sigma.1*I.T
    S.2.4 <- sigma.2*I.T2
    S.2   <- S.2.1+S.2.2+S.2.3+S.2.4
    S.3.1 <- s.comp.3
    S.3.2 <- B.d%*%(S.v.d%*%t(B.d)+Cov.d)%*%Syvd.inv%*%C.d%*%s.comp.1%*%t(B.d)
    S.3.3 <- B.d%*%(S.v.d%*%t(B.d)+Cov.d)%*%a.d%*%(1/a.dt)%*%t(i.T)
    S.3.4 <- B.d%*%(S.v.d%*%t(B.d)+Cov.d)%*%Syu2.inv%*%s.comp.2
    S.3.5 <- sigma.1*I.T%*%Syvd.inv%*%C.d%*%s.comp.1%*%t(B.d)
    S.3.6 <- sigma.1*I.T%*%a.d%*%(1/a.dt)%*%t(i.T)
    S.3.7 <- sigma.1*I.T%*%Syu2.inv%*%s.comp.2
    S.3.8 <- sigma.2*Syvd.inv%*%C.d%*%s.comp.1%*%t(B.d)
    S.3.9 <- sigma.2*(1/a.dt)*t(t(a.d))%*%t(i.T)
    S.3.0 <- sigma.2*Syu2.inv%*%s.comp.2
    S.3   <- S.3.1+S.3.2+S.3.3+S.3.4+S.3.5+S.3.6+S.3.7+S.3.8+S.3.9+S.3.0
    S.4   <- t(S.3)
    CMSE  <- S.1+S.2-S.3-S.4
    if(type=="vector"){
      cmse[which(area==d)] <- c(diag(CMSE)) 
    }
    if(type=="matrix"){
      CMSE.mat[[d]] <- CMSE
    }
    if(type=="components"){
      S.1.mat[[d]] <- S.1
      S.2.mat[[d]] <- S.2
      S.3.mat[[d]] <- S.3
    }
    if(type=="detailed"){
      S.1.1.mat[[d]] <- S.1.1
      S.1.2.mat[[d]] <- S.1.2
      S.1.3.mat[[d]] <- S.1.3
      S.1.4.mat[[d]] <- S.1.4
      S.1.5.mat[[d]] <- S.1.5
      S.1.6.mat[[d]] <- S.1.6
      S.1.7.mat[[d]] <- S.1.7
      S.1.8.mat[[d]] <- S.1.8
      S.1.9.mat[[d]] <- S.1.9
      S.1.0.mat[[d]] <- S.1.0
      S.2.1.mat[[d]] <- S.2.1
      S.2.2.mat[[d]] <- S.2.2
      S.2.3.mat[[d]] <- S.2.3
      S.2.4.mat[[d]] <- S.2.4
      S.3.1.mat[[d]] <- S.3.1
      S.3.2.mat[[d]] <- S.3.2
      S.3.3.mat[[d]] <- S.3.3
      S.3.4.mat[[d]] <- S.3.4
      S.3.5.mat[[d]] <- S.3.5
      S.3.6.mat[[d]] <- S.3.6
      S.3.7.mat[[d]] <- S.3.7
      S.3.8.mat[[d]] <- S.3.8
      S.3.9.mat[[d]] <- S.3.9
      S.3.0.mat[[d]] <- S.3.0
    }
  }
  if(type=="vector"){
    return(cmse)
  }
  if(type=="matrix"){
    return(CMSE.mat)
  }
  if(type=="components"){
    res <- list("S1"=S.1.mat, "S2"=S.2.mat, "S3"=S.3.mat)
    return(res)
  }
  if(type=="detailed"){
    S.1 <- list("S1.1"=S.1.1.mat, "S1.2"=S.1.2.mat, 
                "S1.3"=S.1.3.mat, "S1.4"=S.1.4.mat, 
                "S1.5"=S.1.5.mat, "S1.6"=S.1.6.mat,
                "S1.7"=S.1.7.mat, "S1.8"=S.1.8.mat, 
                "S1.9"=S.1.9.mat, "S1.0"=S.1.0.mat)
    S.2 <- list("S2.1"=S.2.1.mat, "S2.2"=S.2.2.mat, 
                "S2.3"=S.2.3.mat, "S2.4"=S.2.4.mat)
    S.3 <- list("S3.1"=S.3.1.mat, "S3.2"=S.3.2.mat, 
                "S3.3"=S.3.3.mat, "S3.4"=S.3.4.mat, 
                "S3.5"=S.3.5.mat, "S3.6"=S.3.6.mat,
                "S3.7"=S.3.7.mat, "S3.8"=S.3.8.mat, 
                "S3.9"=S.3.9.mat, "S3.0"=S.3.0.mat)
    res <- list("S1"=S.1, "S2"=S.2, "S3"=S.3)
    return(res)
  }
}

# Computes a set of two parametric bootstrap estimators for the MSE of the EBP
Bootstrap <- function(y, x, area, theta, p, D, time, B=20, cov.mat, sigma.e, sigma.v, cov.ev){
  beta.0    <- theta[1]
  beta.1    <- theta[2:(p+1)]
  beta      <- theta[1:(p+1)]
  sigma.1   <- theta[p+2]
  sigma.2   <- theta[p+3]
  z         <- cbind(1,x)
  M         <- time*D
  mu.mat    <- matrix(NA, ncol=B, nrow=M)
  bp.mat    <- matrix(NA, ncol=B, nrow=M)
  ebp.mat   <- matrix(NA, ncol=B, nrow=M)
  G.EBP     <- matrix(NA, ncol=B, nrow=M)
  G1        <- matrix(NA, ncol=B, nrow=M)
  H1.s      <- matrix(NA, ncol=B, nrow=M)
  G1.s      <- matrix(NA, ncol=B, nrow=M)
  G2.s      <- matrix(NA, ncol=B, nrow=M)
  G3.s      <- matrix(NA, ncol=B, nrow=M)
  G4.s      <- matrix(NA, ncol=B, nrow=M)
  CMSE      <- CMSE.MERY(y=y, x=x, area=area, time=time, theta=theta, D=D,
                         sigma.e=sigma.e, sigma.v=sigma.v, cov.ev=cov.ev, type="matrix")
  for(k in 1:B){
    u.1   <- rnorm(D, 0, sqrt(sigma.1))
    u.2   <- rnorm(D*time, 0, sqrt(sigma.2))
    v.mat <- matrix(0, ncol=p+1, nrow=D*time)
    for(d in 1:D){
      cov.mat.d <- cov.mat[which(area==d)]
      v.mat.d   <- matrix(0, ncol=p+1, nrow=time)
      for(t in 1:time){
        cov.mat.dt  <- cov.mat.d[[t]]
        v.mat.d[t,] <- rmvnorm(1, mean=rep(0,p+1), sigma=cov.mat.dt)
      }
      m <- ((d-1)*(time)+1):(d*time)
      v.mat[m,] <- v.mat.d
    }
    e.boot       <- v.mat[,1]
    v.boot       <- v.mat[,2:(p+1)]
    mu.boot      <- c(z%*%beta)+c(v.boot%*%beta.1)+rep(u.1, each=time)+u.2
    y.boot       <- mu.boot+e.boot
    theta.boot   <- MERY(y=y.boot, x=x, area=area, D=D, theta.init=theta, sigma.e=sigma.e,
                         sigma.v=sigma.v, cov.ev=cov.ev, time=time, p=p)
    bp.boot      <- predictMERY(y=y.boot, x=x, area=area, time=time, theta=theta, D=D, p=p,
                                sigma.e=sigma.e, sigma.v=sigma.v, cov.ev=cov.ev)
    ebp.boot     <- predictMERY(y=y.boot, x=x, area=area, time=time, theta=theta.boot, D=D, p=p,
                                sigma.e=sigma.e, sigma.v=sigma.v, cov.ev=cov.ev)
    CMSE.boot    <- CMSE.MERY(y=y, x=x, area=area, time=time, theta=theta.boot, D=D,
                              sigma.e=sigma.e, sigma.v=sigma.v, cov.ev=cov.ev, type="matrix")
    for(d in 1:D){
      mu.boot.d  <- t(t(mu.boot[which(area==d)]))
      bp.boot.d  <- t(t(bp.boot[which(area==d)]))
      ebp.boot.d <- t(t(ebp.boot[which(area==d)]))
      g.mat.d    <- (ebp.boot.d-mu.boot.d)%*%t(ebp.boot.d-mu.boot.d)
      g1.s.mat.d <- (bp.boot.d-mu.boot.d)%*%t(bp.boot.d-mu.boot.d)
      g2.s.mat.d <- (ebp.boot.d-bp.boot.d)%*%t(ebp.boot.d-bp.boot.d)
      g3.s.mat.d <- (ebp.boot.d-bp.boot.d)%*%t(bp.boot.d-mu.boot.d)
      g4.s.mat.d <- t(g3.s.mat.d)
      g1.mat.d   <- CMSE[[d]]
      h1.s.mat.d <- CMSE.boot[[d]]
      G.EBP[((d-1)*time+1):(d*time),k]<- diag(g.mat.d)
      G1[((d-1)*time+1):(d*time),k]   <- diag(g1.mat.d)
      H1.s[((d-1)*time+1):(d*time),k] <- diag(h1.s.mat.d)
      G1.s[((d-1)*time+1):(d*time),k] <- diag(g1.s.mat.d)
      G2.s[((d-1)*time+1):(d*time),k] <- diag(g2.s.mat.d)
      G3.s[((d-1)*time+1):(d*time),k] <- diag(g3.s.mat.d)
      G4.s[((d-1)*time+1):(d*time),k] <- diag(g4.s.mat.d)
    }
    mu.mat[,k]   <- mu.boot
    bp.mat[,k]   <- bp.boot
    ebp.mat[,k]  <- ebp.boot
    cat(k, "\n")
  }
  g.ebp <- rowMeans(G.EBP, na.rm=TRUE)
  g1    <- rowMeans(G1, na.rm=TRUE)
  h1.s  <- rowMeans(H1.s, na.rm=TRUE)
  g1.s  <- rowMeans(G1.s, na.rm=TRUE)
  g2.s  <- rowMeans(G2.s, na.rm=TRUE)
  g3.s  <- rowMeans(G3.s, na.rm=TRUE)
  g4.s  <- rowMeans(G4.s, na.rm=TRUE)
  # g.ebp   <- apply(G.EBP, 1, median)
  # g.1     <- apply(G.1, 1, median)
  # h1.s    <- apply(H1.s, 1, median)
  # g1.s    <- apply(G1.s, 1, median)
  # g2.s    <- apply(G2.s, 1, median)
  # g3.s    <- apply(G3.s, 1, median)
  # g4.s    <- apply(G4.s, 1, median)
  mse.est.1 <- g.ebp
  mse.est.2 <- 2*g1-h1.s+g2.s+g3.s+g4.s
  res.mat   <- as.data.frame(matrix(NA, ncol=2, nrow=M))
  colnames(res.mat) <- paste("Est", 1:2, sep="")
  res.mat$Est1 <- mse.est.1
  res.mat$Est2 <- mse.est.2
  res.mat
}

# Application
mse.est <- Bootstrap(y=y, x=X, area=area, theta=theta.est, p=p, D=D, time=Time, cov.mat=Cov.error,
                     sigma.e=sigma.e, sigma.v=Cov.v, cov.ev=Cov.ev)
mse.est # MSE estimates
# Est1: Full parametric bootstrap estimate
# Est2: Bias-corrected parametric boostrap estimate
