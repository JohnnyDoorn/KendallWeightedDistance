# Combination of methods described in:
# Fagin, R., Kumar, R., & Sivakumar, D. (2003). Comparing top k lists. SIAM Journal on discrete 
#     mathematics, 17, 134–160.
# Kumar, R., & Vassilvitskii, S. (2010). Generalized distances between rankings. In Proceedings
#     of the 19th international conference on world wide web (pp. 571–580).


# Function to compute the weighted, partial Kendall tau distance metric.
# This function takes 2 vectors of integers, x and y, and computes the Kendall distance.
# This distance is basically a bubble sort algorithm, where the number of swaps 
# is the distance. The cost of these swaps can be modified by the different 
# types of weight: similarity, position, and item weights. 
# See the example applications at the bottom of this script

# The function is able to handle partial observations, where not all items from 
# one vector appear in the other. P is the penalty term for items that appear only 
# in 1 vector and not the other. If set to 0, missingness is simply ignored/not punished;
# if set to 1, all missingness is punished. For instance, if "a" appears in x and "b" in y, 
# then it is assumed that if "b" would appear in x, we would need to swap it with "a" to
# make it the same order as in y. If p is set to 0.5, we assume that there is a 50%
# chance they would need to be swapped and therefore the swap costs 0.5 instead of 1.

# The function can also take in a distance matrix, which gives the dissimilarities between
# the items. If a pair of items is highly similar, you want want to punish an inversion
# less severely than if a pair of items is highly dissimilar.
# For instance, if I say "cat" "dog" "bird" and you say "dog" "cat" "bird", we have
# merely swapped cat and dog and have been pretty similar in our answer. Whereas if I
# would have said "dog" "bird" "cat", this could be seen as more dissimilar because
# "bird" and "cat" are not very similar. So even though in both cases only 1 swap is 
# performed to make our answers the same, in the latter case I would be penalized more
# because of the specified dissimilarity matrix.

calcTopTau <- function(x, y, 
                       missingProb = 0, 
                       distMat = NULL, 
                       itemWeights = NULL, 
                       posWeights = NULL, 
                       nTOPK = NULL,
                       printDat = FALSE) {
  
  if ((!is.numeric(x) | !is.numeric(y)) ) {
    warning("Input not numeric. Using conversion to numeric by factorizing. Make sure to specify item and similarity weights in alphabetical order.")
    u <- union(x, y)
    x <- as.numeric(factor(x, levels = u))
    y <- as.numeric(factor(y, levels = u))
  }
  
  # If distance matrix between items is not specified, create a matrix of 1's
  if (is.null(distMat)) {
    distMat <- matrix(1, ncol = max(c(x, y)), nrow = max(c(x, y)))
  }
  
  # If item weights are not specified, create a vector of 1's
  if (is.null(itemWeights)) {
    itemWeights <- rep(1,(max(c(x, y))))
  }
  
  # The y-vector should contain the lowest value, as y will be sorted later
  if (min(c(x, y)) %in% x) {
    z <- y
    y <- x
    x <- z
  }
  
  # Count number of unique items that are not NA:
  u <- union(x, y)
  u <- u[!is.na(u)]
  n <- length(u)
  
  
  # If position weights delta are not specified, create a vector of 1's
  # If a specific algorithm is specified for position weights, use that
  if (!is.null(posWeights) && (length(x) != length(y) | length(x) != n)) {
    # stop("Position weights only work when x and y consist of the same items")
  } else  if (is.null(posWeights)) {
    posWeights <- c(NA,rep(1, length(x)-1))    
  } else if (length(posWeights) == 1 && posWeights == "DCG") {
    posWeights <- c(NA, 1 / (log((2:n) + 1)) - 1 / (log((2:n) + 2)))
  } else if (length(posWeights) == 1 && posWeights == "revDCG") {
    posWeights <- c(NA, 1 / (log((n:2) + 1)) - 1 / (log((n:2) + 2)))
  } 
  # If nTOPK is specified, consider only first nTOPK responses
  if (!is.null(nTOPK)) {
    posWeights <- c(NA, ifelse(2:n <= nTOPK, posWeights[2:n], 0))
  }
  pWeight <- 1
  for(i in 2:n) pWeight[i] <- pWeight[i-1] + posWeights[i]
  
  dist <- 0
  cc <- 0
  # Now loop over all pairs of unique items 
  for(i in 1:(n-1)) {
    for(j in (i+1):n) {

      a <- u[i]
      b <- u[j]
      
      aInX <- a %in% x # check if item 1 is in x
      bInX <- b %in% x 
      aInY <- a %in% y 
      bInY <- b %in% y 
      
      # If equal to 4, it means that a and b are present in both vectors
      nMatches <- sum(c(aInX, aInY, bInX, bInY))
      
      # Cost of swap, if swap is needed
      addThis <- 0 
      
      # Now we check which partial scenario we have for this pair of items a and b. 
      # The cases are described (in a different order) in Fagin 2003:
      if (nMatches == 3) { 
        # 1) One item is missing in one of the vectors 
        #    If that item is not preferred where the pair is complete, + 1, else + 0
        addThis <- switch(which(c(aInX, aInY, bInX, bInY) == FALSE),
                          '1' = which(a == y) < which(b == y),
                          '2' = which(a == x) < which(b == x),
                          '3' = which(b == y) < which(a == y),
                          '4' = which(b == x) < which(a == x))
        
      } else if (nMatches == 2 & ((aInX & bInY) | (bInX & aInY))) {
        # 2) a in x, b in y, or other way around; + 1
        addThis <- 1 
        
      } else if (nMatches == 2 & ((aInX & bInX) | (aInY & bInY))) {
        # 3) a and b in x, none in y, or other way around; + p
        addThis <- missingProb 
        
      } else if (nMatches == 4) {
        # 4) a preferred to b in y, but other way around in x; + 1
        addThis <- (which(a == x) > which(b == x) && which(a == y) < which(b == y)) ||
                   (which(a == x) < which(b == x) && which(a == y) > which(b == y))
        
      }
      
      # Now incorporate the position weights, only when no missingness:
      if (addThis != 0 && length(x) == length(y) &&  length(x) == n) {
        positionCostA <- (pWeight[which(y == a)] - pWeight[which(x == a)]) / (which(y == a) - which(x == a))
        positionCostB <- (pWeight[which(y == b)] - pWeight[which(x == b)]) / (which(y == b) - which(x == b))
        if (is.nan(positionCostA)) positionCostA <- 1
        if (is.nan(positionCostB)) positionCostB <- 1
      } else {
        positionCostA <- positionCostB <- 1
      }

      timesThis <- 1
      # Now incorporate the dissimilarity matrix:
      if (all(!is.na(c(a, b))) & (a != b)) 
        timesThis <- ifelse(is.na(distMat[a, b]), mean(distMat, na.rm = TRUE), distMat[a, b])
   
      # calculate the cost of the swap and add it to the total distance 
      dist <- dist + addThis * timesThis * itemWeights[a] * itemWeights[b] * positionCostA * positionCostB
    }
  }
  
  # If desired, print the sorted vectors, to see the pairs/order:
  if (printDat) print(cbind(x,y))
  
  return(dist)
}





