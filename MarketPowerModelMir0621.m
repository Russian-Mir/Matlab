%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%THE STOLYPIN REFORMS AND THE RUSSIAN MIR
%A GENERAL EQUILIBRIUM MODEL OF AGRARIAN TRANSITION
%WITH MARKET POWER WITH HETEROGENEOUS AGENTS
% by Aleksandr Michuda and Jonathan Conning  
% MARCH 2014    

% Description:  We designed this 'MarketPowerModel' class to create economies
% with PROPERTIES (e.g. production technology parameters, 
% factor endowments and a distribution of skills and factors; default 
% values are below but these can be changed from outside ) 
% and METHODS or functions that solve for equilibrium allocations under the 
% assumption of competitive markets and market-power distorted markets, 
% and other things.
% 
% One must invoke an instance of this class to analyze results 
% (e.g.  mm = MarketPowerModel) from command line or program.


%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%PRELIMINARIES
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


classdef MarketPowerModelMir0621 < handle
    properties
      alpha     = 0.6     % alpha (land) for production function
      gamma     = 0.8    % homogeneity factor
      Tbar      = 100    % Land Endowment
      Lbar      = 100     % Labor Endowment
      mu        = 1   % first moment of lognormal distribution
      sigma     = .2      % second moment of lognormal distribution
      N         = 5       % # of quantiles (number of farms)
      numscenes = 5       % # of land concentration scenarios
      H         = 0     % Fixed Cost to Production
      wstar     = 0       % empty property competitive eqn price vector  
      Tstar     = 0       % Competitive Land allocation vector
      Lstar     = 0       % Competitive Labor allocation vector
      zweight   = 0       % skill level vector for option 'popweight'
      zconstant = 0       % skill level vector for option 'constant'
      quantiles= [1 2 3 4 5]   % Vector of quantiles 
      frequency= 0
      LatTrstar = 0       % Market Power Land allocation vector
      LatLrstar = 0       % Market Power Labor allocation vector
      wrLat     = 0      % Market Power distorted wages and rentals
      A         = 1      % Scaling parameter 
      p         = 1      % Price
      weights   = 0
      calparams = 0
      MirTrstar = 0
      MirLrstar = 0
      wrMir     = 0
      ubar      = 10
    end
    
    methods
        
        function self = MarketPowerModelMir(mu, sigma)
        % constructor method to pass arguments to initialize properties
           switch nargin
               case 0 %change nothing
               case 2
                 self.mu= mu;
                 self.sigma=sigma;
               otherwise
                 beep
                 warning('MKTPOWER: 0 or 3 args! e.g. (10,5,''constant''); reverting to defaults');
           end
        end        
        
        function [G]= skill(self, params, popoption, quantiles) 
            % returns a vector of farming skill levels drawn from 
            % lognormal (mu, sigma and N are local)
            
            N= self.N;
            mu= params(1);
            sigma= params(2);   
            fun= @(X)X.*lognpdf(X, mu, sigma);
            
            
            %%defines different options depending on what kind of skill
            %%vector is needed.
            if strcmp(popoption,'constant')== 1 
                %%Gives the same population per quantile.
                cuts = zeros(1, N);       % pre-allocate cutoffs array
                G    = zeros(1, N);       % pre-allocate conditional skill array
                cuts(1) = 0; xg = 1;     % first cutoff, guess at next

                for j= 1:N -1
                    f  = @(X)logncdf(X, mu, sigma)- j/N;
                    cuts(j+1)  = fsolve(f, xg, optimset('Display', 'off'));
                    xg = cuts(j+1)*(1+1/N);  %move up the guess value (1/N)%
                end
            %display(cuts');
                cuts(N+1)=inf;
                for j= 1:N-1
                    CS= N.*integral(fun, cuts(j), cuts(j+1));
                    G(1,j)= CS;
                end
                G(1,N) = N.*integral(fun, cuts(N), inf);
                self.zconstant= G;
            elseif strcmp(popoption, 'popweight')== 1
                %%gives the densities for a any sized quantile.
                cuts= quantiles;
                for j= 1:numel(quantiles)-1
                    CS= self.N.*integral(fun, quantiles(j), quantiles(j+1));
                    G(j+1)=CS;
                end
                G(1)= self.N.*integral(fun, 0, quantiles(1));
                G(numel(quantiles)+1)= self.N.*integral(fun, quantiles(numel(quantiles)), inf);
                self.zweight= G;
            end         
        end 
        
        
      

        function [Y]= ProdFunction(self, T, L, z)
            %A Cobb-Douglas production function which has decreasing. 
            % returns to scale.
            A= self.A;
            Y= A*z*((T^self.alpha)*(L^(1-self.alpha)))^self.gamma;
        end
        

        function [Y]= Weights(self, params,quantiles)
            %This function calculates the density in each quantile given
            %by any vector.
            mu= params(1);
            sigma= params(2);
            %z= skill(self, params, 'popweight', quantiles);
            M= size(quantiles);
            Y(1)= logncdf(quantiles(1), mu, sigma)- logncdf(0, mu, sigma);
            for j= 2:M(2)
                Y(j)= logncdf(quantiles(j), mu, sigma)- logncdf(quantiles(j-1), mu, sigma);
            end
            Y(M(2)+1)= logncdf(inf, mu, sigma)- logncdf(quantiles(M(2)), mu, sigma);
            self.weights= Y;
        end
        
        
        
        function [Excess Landstar Laborstar]= SolveBlock(self, w, Land, Labor, params, popoption, MP,quantiles) 
            %This is the workhorse of the model. It defines a vector of
            %conditional
            %demand functions, throws farmers out of production given some
            %fixed cost, and defines excess demands to be used later in
            %figuring out a price vector in equilibrium.
            
            Popn= self.Lbar;
            gamma= self.gamma;
            alpha= self.alpha;
            wa= w(2);
            r=w(1);
            p= self.p;
            A= self.A;
            % Excess demands and vectors of land demands.
            if strcmp(popoption,'popweight')== 1 
                % weights based on a random vector.
                if strcmp(MP, 'no')==1
                    z= skill(self, params, popoption, quantiles);
                    Weight= Weights(self, params,quantiles);                
                elseif strcmp(MP, 'yes')==1
                    z1= skill(self,params, popoption, quantiles);
                    z= z1(1:numel(z1)-1);
                    W= Weights(self, params,quantiles);
                    Weight= W(1:numel(W)-1);
                end
            elseif strcmp(popoption, 'constant')== 1
                %assumes the same population in each quantile.
                Weight= 1/self.N;
                if strcmp(MP, 'no')==1
                    z=self.zconstant;
                elseif strcmp(MP, 'yes')==1
                    z= self.zconstant(1:self.N-1);
                end
            end   
            M= size(z);
            function [Y]= CompProfit(self, T,L, w, z)
                % vector farm profits for input vector (T,L) and prices w
                Y = ProdFunction(self, T, L, z) - w(1)*T- w(2)*L - self.H;
            end
            for j= 1:M(2)  %I changed this from N because SolveBlock wasn't allowing 
                %%%skill vectors of less than N rows. Need this later for
                %%%the Market power equilibrium.
                LandDemand(j)= ((wa/(gamma.*z(j).*A.*p.*(1-alpha))).*...
                    (((1-alpha)/alpha).*(r/wa))...
                    .^(1-gamma.*(1-alpha))).^(1/(gamma-1));
                LaborDemand(j)=((r/(gamma.*z(j).*A.*p.*alpha))* ...
                    ((alpha/(1-alpha)).*(wa/r)).^(1-gamma*alpha)...
                    ).^(1/(gamma-1));
                if CompProfit(self,LandDemand(j), LaborDemand(j), w, z(j))< 0
                    LaborDemand(j)=0;
                    LandDemand(j)=0;
                    %%%%This if statement takes into account farm
                    %%%%profits and takes farmers out of production if
                    %%%%their profits are less than zero given some fixed
                    %%%%cost to production 
                end
            end
 
            Excess= [sum(Popn.*Weight.*LandDemand)...
                ; sum(Popn.*Weight.*LaborDemand)]- [Land;Labor];
            Landstar= Popn.*Weight.*LandDemand;
            Laborstar= Popn.*Weight.*LaborDemand;
        end
        
        


        function [Y]=CompetitiveEq(self, Land, Labor, params, popoption)
            %%This uses the solveblock function and its excess demands and
            %%finds a root which corresponds to an equilibrium price
            %%vector.
            f= @(w)SolveBlock(self, w, Land, Labor, params, popoption, 'no',self.quantiles);
            w0= [1,1];
            Y= fsolve(f, w0, optimset('Display', 'off'));
            self.wstar=Y;
        end 
        
        function [Y]=DistortedEq(self, Land, Labor, params, popoption) 
            %%This is the same as CompetitiveEq, but it doesn't save the
            %%price vector as a property. This will be used in the market
            %%power equilibrium functions.
            f= @(w)SolveBlock(self, w, Land, Labor, params, popoption, 'yes',self.quantiles);
            w0= [1,1];
            Y= fsolve(f, w0, optimset('Display', 'off'));
        end
%%THis is sthisamymrgwdhwfbh


%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%EQUILIBRIA UNDER DIFFERENT SPECIFICATIONS
% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%This function is in charge of all scenarios apart from the straight
%competitive equilibrium. Each scenario corresponds to a combination of
%markers:
%1. ****mir==yes and efficient==yes
%--------This scenario is of a cartel maximizing earnings and extracting
%any surplus, lump sum.
%2. ****mir=yes and efficient==no
%--------This scenario is of a cartel maximizing profits, with the mir
%present.
%3. ****mir==no and efficient==no
%--------This scenario is of a cartel maximizing profits, but with a
%competitive fringe, a la Latifundia Economics.

        function [w]= MirPrice(self,TL)
            z=self.zconstant;
            Tbar=self.Tbar;
            Lbar=self.Lbar;
            N=self.N;
            alpha=self.alpha;
            w(1)= (1/80)*sum(z(1:N-1))*self.gamma*self.alpha*(Lbar/N)*(1/(N-1))...
                *(((((Tbar-(Lbar/N)*TL(1))/((N-1)*(Lbar/N)))^self.alpha)*((Lbar-(Lbar/N)*TL(2))/(N-1)*(Lbar/N))...
                ^(1-self.alpha))^self.gamma)/((Tbar-(Lbar/N)*TL(1))/((N-1)*(Lbar/N)));
            w(2)= (1/80)*sum(z(1:N-1))*self.gamma*(1-self.alpha)*(Lbar/N)*(1/(N-1))...
                *(((((Tbar-(Lbar/N)*TL(1))/((N-1)*(Lbar/N)))^alpha)*((Lbar-(Lbar/N)*TL(2))/(N-1)*(Lbar/N))...
                ^(1-self.alpha))^self.gamma)/((Lbar-(Lbar/N)*TL(2))/((N-1)*(Lbar/N)));
        end
        
        function [Y]= EfficientExploitation(self)
            N=self.N;
            function [J]= Objective(self, Tr,Lr,R)
                for i=1:N-1
                    J= -(ProdFunction(self, Tr, Lr, zBG)+sum(R(i)));
                    
                end
            end
        end



        function [Y]= BGEarn(self, TL, theta, params, popoption,quantiles,mir, efficient) 
            %%This is function which defines the maximization problem for a
            %%landlord who wants to exert market power.  Returns total
            %%earnings for given input vector TL.  
            N= self.N; 
            if strcmp(popoption,'popweight')== 1 
                % weights based on an any-sized vector.
                Weight= logncdf(inf, params(1), params(2))- ...
                    logncdf(quantiles(numel(quantiles)), params(1), params(2));
                z= self.zweight;
            elseif strcmp(popoption, 'constant')== 1
                %assumes the same population in each quantile.
                Weight= 1/self.N;
                z=self.zconstant;
            end 
            Popn= self.Lbar; % population
            zBG= max(z); %landlord skill
            Tbar= self.Tbar;
            Lbar= self.Lbar;
            alpha= self.alpha;
            gamma= self.gamma;
            Lr= TL(2);
            Tr= TL(1);
           
            if strcmp(mir, 'yes')==1
                if strcmp(efficient, 'yes')==1
                    R=TL(3);
                    Y= -(ProdFunction(self, Tr, Lr, zBG)+R);
                elseif strcmp(efficient, 'no')==1
                    
                    % This is when the MIR is involved (egalitarian
                    % allocations) and inefficient methods by the cartel
                    % w(1) and w(2) are the partial derivatives of land and
                    % labor, respectively, of the communal production
                    % function with respect to the factor choice of the
                    % cartel.
                    w= MirPrice(self,[Tr Lr]);
                    Y= -(Lbar/N)*((zBG*((Tr^alpha)*(Lr^(1-alpha)))^gamma)- w(2)*Lr...
                        -w(1)*(Tr-(Tbar)*((1/Weight)*(1/Popn))*(theta)));
                      
                end
            elseif strcmp(mir, 'no')==1
                % No MIR involved so dealing with a competitive fringe
                w = DistortedEq(self, Tbar- (Popn*Weight)*Tr, Lbar- (Popn*Weight)*Lr, params, popoption);
                Y = -(Lbar/N)*((zBG*((Tr^alpha)*(Lr^(1-alpha)))^gamma)- w(2)*Lr...
                    -w(1)*(Tr-(Tbar)*((1/Weight)*(1/Popn))*(theta)));
            end
                
  

            % Fringe economy gets what landlord does not use                 
            

        end
        
        function [Y]= MaxProfitCal(self, params, theta)
            TL0= [1 1];
            N= self.N;
            Popn=self.Lbar;
            f= @(TL)BGEarn(self, TL, theta, params, 'popweight');
            Y= fminsearch(f, TL0, optimset('Display','iter'));
        end
        
        
        function [w, Lat, Mir]=MaxProfit(self, popoption, params,quantiles,mir, efficient) 
            %This minimizes the negative of earnings, finding a maximum.
            % returns distorted factor price vector, landlord labor and land demand
            N= self.N;
            Popn= self.Lbar;
            Tbar= self.Tbar;
            Lbar=self.Lbar;
            z= self.zconstant;
            Lat=0;
            Mir=0;
            function [c, ceq]= mycon(TL,i)
                  w=MirPrice(self,TL);
                c= ((Lbar/N)*(sum(z(1:N-1))*(((((1-(i/self.numscenes))*Tbar))/((N-1)*(Lbar/N)))^self.alpha)*...
                    (((Lbar)/((N-1)*(Lbar/N)))...
                    ^(1-self.alpha)))^self.gamma)-((Lbar/N)*(sum(z(1:N-1))*((((Tbar-(Lbar/N)*TL(1))/((N-1)*(Lbar/N)))^self.alpha)*...
                    (((Lbar-(Lbar/N)*TL(2))/((N-1)*(Lbar/N)))...
                    ^(1-self.alpha)))^self.gamma)+w(2)*((Lbar/N)*TL(2))...
                    + w(1)*((Lbar/N)*TL(1)-((i/self.numscenes)*Tbar)));
                ceq=0;
            end
            
            function [c, ceq]= myconED(TL)
                c= self.ubar + TL(3)-(Lbar/N)*(sum(z(1:N-1))*((((Tbar-(Lbar/N)*TL(1))/((N-1)*(Lbar/N)))^self.alpha)*...
                    (((Lbar-(Lbar/N)*TL(2))/((N-1)*(Lbar/N)))...
                    ^(1-self.alpha)))^self.gamma); %%%Setting up constraint function for ED case
                ceq=0;                             %%% Mir Production - the rent has to be larger than some 
            end                                    %%% subsistence minimum ubar.
%             for j= 1:self.numscenes
%                 f= @(TL)BGEarn(self, TL, j/self.numscenes, params, popoption,quantiles,mir, efficient);
%                 G{j,1}= fminsearch(f, TL0, optimset('Display', 'iter'));
%             end
%                 J= G{i,:};  %%%%Breaking up the cell array into a vector

                if strcmp(mir, 'no')
                    TL0= [1 1];
                                
                    for j= 1:self.numscenes
                        f= @(TL)BGEarn(self, TL, j/self.numscenes, params, popoption,quantiles,mir, efficient);

                        G{j,1}= fminsearch(f, TL0, optimset('Display', 'iter'));
                    end
                    for i= 1:self.numscenes
                        f= @(TL)BGEarn(self, TL, j/self.numscenes, params, popoption,quantiles,mir, efficient);

                        J= G{i,:};  %%%%Breaking up the cell array into a vector
                        
                        Lat(1,i)=J(1); %%Labor
                        Lat(2,i)=J(2); %% Land
                    end
                elseif strcmp(mir, 'yes')
                    if strcmp(efficient, 'no')
                        TL0= [1 1];
                        
                        for j= 1:self.numscenes
                            f= @(TL)BGEarn(self, TL, j/self.numscenes, params, popoption,quantiles,mir, efficient);
                                           
                            G{j,1}= fmincon(f, TL0,[],[],[],[],[],[]...
                                ,@(TL)mycon(TL,j), optimset('Display', 'iter','Algorithm','interior-point'));
                        end
                        for i= 1:self.numscenes
                            f= @(TL)BGEarn(self, TL, j/self.numscenes, params, popoption,quantiles,mir, efficient);

                            J= G{i,:};  %%%%Breaking up the cell array into a vector
                            
                            Mir(1,i)=J(1);
                            Mir(2,i)=J(2);
                        end
                    elseif strcmp(efficient, 'yes')
                        TL0= [1 1 1];
                        for j=1:self.numscenes
                            f= @(TL)BGEarn(self, TL, j/self.numscenes, params, popoption,quantiles,mir, efficient);

                            G{j,1}= fmincon(f,TL0, [],[],[],[],[],[],...
                                @(TL)myconED(TL),optimset('Display', 'iter', 'Algorithm', 'interior-point'));
                        end
                        for i= 1:self.numscenes
                            
                            J= G{i,:};  %%%%Breaking up the cell array into a vector
                            
                            Mir(1,i)=J(1);
                            Mir(2,i)=J(2);
                            Mir(3,i)=J(3);
                        end
                        
                    end
                end

            if strcmp(popoption, 'popweight')==1
                Weight= logncdf(inf, params(1), params(2))- ...
                    logncdf(quantiles(numel(quantiles)), params(1), params(2));
            elseif strcmp(popoption, 'constant')==1
                Weight= 1/N;
            end
            if strcmp(mir, 'no')
                self.LatTrstar= (Popn*Weight)*Lat(1,:);
                self.LatLrstar= (Popn*Weight)*Lat(2,:);
                for i= 1:self.numscenes
                    u{i,1}= DistortedEq(self, self.Tbar-self.LatTrstar(i), self.Lbar- ...
                        self.LatLrstar(i), params, popoption);
                end
                for i= 1:self.numscenes
                    V= u{i,:}; %%%%%Breaking up the cell array into a vector
                    w(1,i)= V(1);
                    w(2,i)= V(2);
                end
                self.wrLat= w; %%%%%Getting distorted wages and rentals
            elseif strcmp(mir, 'yes')
                if strcmp(efficient, 'no')
                    
                    self.MirTrstar= (Popn*Weight)*Mir(1,:);
                    self.MirLrstar= (Popn*Weight)*Mir(2,:);
                    for i= 1:self.numscenes
                        m= MirPrice(self, [Mir(1,i) Mir(2,i)]);
                        w(1,i)= m(1);
                        w(2,i)= m(2);
                    end
                    self.wrMir=w;
                elseif strcmp(efficient, 'yes')
                    self.MirTrstar= (Popn*Weight)*Mir(1,:);
                    self.MirLrstar= (Popn*Weight)*Mir(2,:);
                    R= Mir(3,:);
                    w=0;
                end
            end

            
        end
        
        function [Peasant, Cartel]= FactorIncome(self, regime)
            z= self.zconstant;
            Tbar=self.Tbar;
            Lbar= self.Lbar;
            alpha=self.alpha;
            gamma=self.gamma;
            N= self.N;
            if strcmp(regime, 'DD')
                for i=1:self.numscenes
                    for j=1:N-1
                        Peasant(i,j)= (Lbar/N)*(z(j)*((((Tbar-self.MirTrstar(i))/((N-1)*(Lbar/N)))^self.alpha)*...
                            (((Lbar-self.MirLrstar(i))/((N-1)*(Lbar/N)))...
                            ^(1-self.alpha)))^self.gamma)+self.wrMir(2,i)*(self.MirLrstar(i)/(N-1))...
                            + self.wrMir(1,i)*(self.MirTrstar(i)-((i/self.numscenes)*Tbar))/(N-1);
%                         if Peasant(i,j)<0
%                             Peasant(i,j)=0;
%                         end
                    end
                    Cartel(i)= (Lbar/N)*ProdFunction(self, self.MirTrstar(i)*(N/Lbar),self.MirLrstar(i)*(N/Lbar),z(N))...
                        - self.wrMir(2,i)*self.MirLrstar(i)...
                        + self.wrMir(1,i)*(i/self.numscenes)*(Tbar)...
                        - self.wrMir(1,i)*(self.MirTrstar(i));

                end
%                 

%                 Cartel= TotalProd(self,'DD')- Peasant;
                                
                elseif strcmp(regime, 'DE')
                for i=1:self.numscenes
                    for j=1:N-1
                [~, Landstar, Laborstar]= SolveBlock(self, self.wrLat(:,i), Tbar-self.LatTrstar(i),...
                    Lbar-self.LatLrstar(i),[self.mu self.sigma],'constant','yes',self.quantiles);
                    Peasant(i,j)= (Lbar/N)*ProdFunction(self, Landstar(j)*(N/Lbar),Laborstar(j)*(N/Lbar),z(j))-...
                        self.wrLat(2,i)*Laborstar(j)+self.wrLat(2,i)*(Lbar/(N-1))...
                        +(((1-(i/self.numscenes))*Tbar)/(N-1))*self.wrLat(1,i)-self.wrLat(1,i)*Landstar(j);
                    Cartel(i)= (Lbar/N)*ProdFunction(self, self.LatTrstar(i)*(N/Lbar),self.LatLrstar(i)*(N/Lbar),z(N))...
                        - self.wrLat(2,i)*self.LatLrstar(i)...
                        + self.wrLat(1,i)*(i/self.numscenes)*(Tbar)...
                        - self.wrLat(1,i)*(self.LatTrstar(i));

                    end
                end
            elseif strcmp(regime, 'EE')
                w= CompetitiveEq(self, Tbar, Lbar, [self.mu self.sigma], 'constant');
                for j=1:self.numscenes
                    for i=1:N-1
                        [~, Landstar, Laborstar]= SolveBlock(self, w, Tbar,...
                            Lbar,[self.mu self.sigma],'constant','no',self.quantiles);
                        Peasant(i,j)= (Lbar/N)*ProdFunction(self, Landstar(i)*(N/Lbar),Laborstar(i)*(N/Lbar),z(i))...
                            -w(2)*Laborstar(i)+w(2)*((Lbar/(N-1)))+w(1)*(((1-(j/self.numscenes))*Tbar)/((N-1)))...
                            -w(1)*Landstar(i);
                        Cartel(j)= (Lbar/N)*ProdFunction(self, Landstar(N)*(N/Lbar),Laborstar(N)*(N/Lbar),z(N))...
                            -w(2)*Laborstar(N)+ w(1)*(j/self.numscenes)*Tbar- w(1)*Landstar(N);
                    end
                end

            end
        end
        
        function [Peasant,Cartel,Total]= TotalProd(self,regime)
            z=self.zconstant;
            Tbar=self.Tbar;
            Lbar=self.Lbar;
            N=self.N;
            if strcmp(regime,'DD')
                for i=1:self.numscenes
                    Peasant(i)= (Lbar/N)*(sum(z(1:N-1))*((((Tbar-self.MirTrstar(i))/((N-1)*(Lbar/N)))^self.alpha)*...
                        (((Lbar-self.MirLrstar(i))/((N-1)*(Lbar/N)))...
                        ^(1-self.alpha)))^self.gamma);
                    Cartel(i)=(Lbar/N)*(max(z)*(((self.MirTrstar(i)*(N/Lbar))^self.alpha)*((self.MirLrstar(i)*(N/Lbar))...
                        ^(1-self.alpha)))^self.gamma);
                end
                Total=Peasant+Cartel;
            elseif strcmp(regime,'DE')
                for i=1:self.numscenes
                    for j=1:N-1
                        [~, Landstar, Laborstar]= SolveBlock(self, self.wrLat(:,i), Tbar-self.LatTrstar(i),...
                            Lbar-self.LatLrstar(i),[self.mu self.sigma],'constant','yes',self.quantiles);
                        Peasant2(i,j)= (Lbar/N)*ProdFunction(self, Landstar(j)*(N/Lbar),Laborstar(j)*(N/Lbar),z(j));
                        Cartel(i)=(Lbar/N)*ProdFunction(self, self.LatTrstar(i)*(N/Lbar),self.LatLrstar(i)*(N/Lbar),z(N));
%                         Cartel(i)=(Lbar/N)*(max(z)*(((self.LatTrstar(i)*(N/Lbar))^self.alpha)...
%                             *((self.LatLrstar(i)*(N/Lbar))^(1-self.alpha)))^self.gamma);
                        
                    end
                end
                Peasant=(sum(Peasant2,2));
                Total=Peasant+ transpose(Cartel);
            elseif strcmp(regime, 'EE')
                w= CompetitiveEq(self, Tbar, Lbar, [self.mu self.sigma], 'constant');
                Peasant= 0;
                Cartel= 0;
                for i=1:N
                [~, Landstar, Laborstar]= SolveBlock(self, w, Tbar,...
                    Lbar,[self.mu self.sigma],'constant','no',self.quantiles);
                Total(i)=(Lbar/N)*ProdFunction(self, Landstar(i)*(N/Lbar)...
                    ,Laborstar(i)*(N/Lbar),z(i));
                end
            end
        end

        function [Y]= DistLand(self, popoption, params)
            %%This defines the distorted land vector
            for i= 1:self.numscenes
                ww= self.wrd(:,i);
               [~,J,~]= SolveBlock(self, ww, self.Tbar-self.Trstar(i)...
                    , self.Lbar-self.Lrstar(i), params, popoption, 'yes');
                Y(:,i)= J(:);
            end
            Y= vertcat(Y, self.Trstar);
        end        

        function [Y]= DistLabor(self, popoption, params)
            %%This defines the distorted labor vector.
            for i= 1:self.numscenes
                ww= self.wrd(:,i);
               [~,~,J]= SolveBlock(self, ww, self.Tbar-self.Trstar(i)...
                    , self.Lbar-self.Lrstar(i), params, popoption, 'yes');
                Y(:,i)= J(:);
            end
            Y= vertcat(Y, self.Lrstar);
        end  
        
         function [Y]= CalDistLand(self, theta, params,quantiles)
            %%This defines the distorted land vector
            Weight= logncdf(inf, params(1), params(2))- ...
                logncdf(quantiles(numel(quantiles)), params(1), params(2));
            M= numel(self.zweight);
            MP= MaxProfitCal(self, params, theta);
            Tr= MP(1);
            Lr= MP(2);
            ww= DistortedEq(self, self.Tbar- (self.Lbar*Weight)*Tr,...
                self.Lbar- (self.Lbar*Weight)*Lr, params, 'popweight');
            [~,J,~]= SolveBlock(self, ww, self.Tbar-(self.Lbar*Weight)*Tr...
                , self.Lbar-(self.Lbar*Weight)*Lr, params, 'popweight', 'yes');
            Y= vertcat(transpose(J), self.Lbar*Weight*MP(1));
        end       
              
       function [calgoods]= calibrate(self,quantiles)
           %%Given some quantiles, this function attempts to find the underlying
           %%skill distribution of the economy in question, by minimizing
           %%the distance between the quantiles and a competitive land
           %%distribution generated by the model.
           params0= [2 2];
           freqWeight= self.frequency/sum(self.frequency);
           function [Y]= Landstar(self, w, Land, Labor, params,quantiles)
              [~, Y, ~]= SolveBlock(self, w, Land, Labor, params, 'popweight', 'no',quantiles);
           end
           
          
           for i=1:numel(quantiles)-1
               meanQuant(i)= (quantiles(i)+quantiles(i+1))/2;
           end
           
           WeightData= meanQuant.*freqWeight;
%            %meanData(1)= ((quantiles(1)/2)*(frequency(1)/F);
%            meanData= sum(WeightData);
%            varData= var(meanQuant, self.frequency);
%            skewnessData=sum(freqWeight.*(meanQuant-meanData).^3)/varData;
%            for i= 1:numel(meanQuant)
%                data(i:self.frequency(i))=meanQuant(i);
%            end
           edgelow=1;
           for i= 1:numel(meanQuant)
              edgehigh = edgelow +self.frequency(i) - 1;
              data(edgelow:edgehigh) = meanQuant(i);
              edgelow = edgehigh +1;
           end


           [logpar]=lognfit(data);
           calDist= skill(self, logpar, 'popweight', quantiles);
           
%            f= @(params)(calDist- scaledata(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                  self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params),0,max(calDist)));
           
                          
          % muLand = log((m.^2)/sqrt(v+m.^2));
           %sigmaLand = sqrt(log(v/(m.^2)+1));
%             f= @(params)([meanData; varData; skewnessData]- ...
%                 [mean(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params));...
%                 var(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params));
%                 skewness(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params))]);
%             f= @(params)([meanData- mean(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params))]);
%                 varData- var(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params));
%                 skewnessData-skewness(Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params))]);
                
%             g=@(params)quantiles- Landstar(self, CompetitiveEq(self, self.Tbar, ...
%                 self.Lbar, params, popoption), self.Tbar, self.Lbar, params, popoption);

           %calblunt= fsolve(g, params0, optimset('Display', 'iter'));

%            calgoods= fsolve(f, logpar,optimset('Display','iter'));
           calgoods=lsqcurvefit(@(params,quantiles)(scaledata(Landstar(self, CompetitiveEq(self, self.Tbar, ...
                  self.Lbar, params, 'popweight'), self.Tbar, self.Lbar, params,quantiles),0,max(calDist)))...
                  ,logpar, quantiles, calDist,[],[], optimset('Display','iter')); 
           self.calparams=calgoods;
       end
       
       function [thetastar]= marketPowerCalibrate(self, data,params, theta0, theta1)
           threshold= 1e-04;
           thetastar=0;
           pop= transpose(self.weights);
           gini1= ginicoeff(pop, data)-ginicoeff(pop,CalDistLand(self, theta1, params));
           %ginistar= ginicoeff(pop, quantiles)-ginicoeff(pop,CalDistLand(self, (theta1+theta0)/2, params));
           gini0= ginicoeff(pop, data)-ginicoeff(pop,CalDistLand(self, theta0, params));
           ginistar= ginicoeff(pop, data)-ginicoeff(pop,CalDistLand(self, ...
              theta1- (gini1)/((gini1-gini0)/ (theta1-theta0)) , params));
           while abs(theta0-theta1)>threshold
               theta1a= theta1;
               theta0a= theta0;
               
               if abs(ginistar)<= threshold
                   break;
               elseif (ginistar)*(gini1)< 0
                   theta0=thetastar;
               else
                   theta1= thetastar;
               end
               if abs(theta1-theta1a)==0
                   gini1=gini1;
               else
                   gini1= ginicoeff(pop, data)-ginicoeff(pop,CalDistLand(self, theta1, params));
               end
               if abs(theta0a-theta0)==0
                   gini0=gini0;
               else
                   gini0= ginicoeff(pop, data)-ginicoeff(pop,CalDistLand(self, theta0, params));
               end
               %%%%Bisection method (230 seconds for theta=.654)
               %thetastar=(theta0+theta1)/2;               
               %%%%Secant method (149 seconds for theta=.654)
                thetastar= theta1- (gini1)/((gini1-gini0)/ (theta1-theta0));
               ginistar= ginicoeff(pop, data)-ginicoeff(pop,CalDistLand(self,...
                   thetastar, params));
           end
       end
    end
                
end
            
   
     
