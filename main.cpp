#include <algorithm>
#include <vector>
#include <queue>
#include <map>
#include <sstream>
#include <iterator>
#include <ctime>
using namespace std;

const int DEGREE = 5;
const int VARIABLES = 15;
const int SENSITIVITY = 15; // Should be less or equal than VARIABLES
// Set sensitivity equal to -1 to try fully processing every single symmetrization polynomial of <= VARIABLES and <= DEGREE

#define DEBUG_OUTPUT
#define LIGHT_DEBUG_CODE
//#define HEAVY_DEBUG_CODE

#define CHECK_DEGREE_CONDITIONS
#define SOLVE_SYSTEM_OF_EQUATIONS
#define CHECK_VARIABLE_PERMUTATIONS

//#define WEIRD_OPTIMIZATION

#ifdef CHECK_DEGREE_CONDITIONS
bool satisfiesDegreeConditions(int* container, int positionToTest, int maxAllowedDegree);
#endif

// ====================================================================================================================
// Math Functions
// ====================================================================================================================

int binom[VARIABLES + 1][VARIABLES + 1]; // binom[15][7] = 6435, binom[21][10] = 352716

void initializeBinomialCoefficients()
{
    for (int n = 0; n <= VARIABLES; ++n)
        for (int k = 0; k <= VARIABLES; ++k)
            if (n < k) binom[n][k] = 0; else
                if (k == 0) binom[n][k] = 1; else
                    binom[n][k] = binom[n-1][k] + binom[n-1][k-1];
}

// --------------------------------------------------------------------------------------------------------------------

// template <

long long gcd(long long a, long long b)
{
    if (b == 0) return a;
    return gcd(b, a % b);
}

int gcd(int a, int b)
{
    if (b == 0) return a;
    return gcd(b, a % b);
}

// --------------------------------------------------------------------------------------------------------------------

int countBits(int x)
{
    int res = 0;
    while (x != 0)
    {
        x = x & (x - 1);
        ++res;
    }
    return res;
}

// ====================================================================================================================
// Generation of Symmetrization Polynomials
// ====================================================================================================================

struct SymmetrizationPolynomial
{
    SymmetrizationPolynomial(int degree_in, int variables_in, int* q_in)
    {
        variables = variables_in;
        q.resize(variables_in + 1);
        for (int i = 0; i <= variables_in; ++i) q[i] = q_in[i];
        degree = degree_in;
    }

	void saveSplitPositions()
	{
		// ...
		splitPosition.clear();
	}

	void loadSplitPositions()
	{
		// ...
	}

    char variables; // The number of variables of the corresponding Boolean functions
    vector<short> q; // The integer values of symmetrization polynomial    
    char degree; // The minimum degree of the corresponding Boolean functions
	vector<pair<int, int> > splitPosition; // Position numbers of q_0 and q_1 for each of the valid splits
};

// Stores all the symmetrization polynomials that have a full decomposition
vector<SymmetrizationPolynomial> poly;
// Contain the leftmost and the rightmost indices of poly that contain symmetrization polynomials on i variables.
int leftMostPolynomialIndex[VARIABLES + 1], rightMostPolynomialIndex[VARIABLES + 1];

// --------------------------------------------------------------------------------------------------------------------

// For a symmetrization polynomial of size "variables",\
// the points k = {0, variables, 1, variables - 1, ...} have the least number of possible values:
// from 0 to \binom{variables}{k[i]}
void initializeCombinations(int degree, int variables, int* index, int* value, int* minValue, int* maxValue)
{
    if (degree > variables)
    {
        printf("Trying to initialize combinations for a bigger degree than the number of variables.\n");
        system("pause");
    }
    int left = 0, right = variables;
    for (int i = 0; i <= degree; ++i)
    {
        if (i % 2 == 0)
            index[i] = left++;
        else
            index[i] = right--;
        if (value != NULL) // Sometimes the parameters value, minValue and maxValue are not passed into this method
        {
            value[i] = minValue[i] = 0;
            maxValue[i] = binom[variables][index[i]];
        }
    }
}

// --------------------------------------------------------------------------------------------------------------------

// Find the lexicographically next combination of values
bool generateNextCombination(int degree, int* value, int* minValue, int* maxValue)
{
    for (int i = degree; i > -1; --i)
        if (value[i] < maxValue[i])
        {
            ++value[i];
            for (int j = i + 1; j <= degree; ++j) value[j] = minValue[j];
            return true;
        }
    return false;
}
// --------------------------------------------------------------------------------------------------------------------

// Interpolating the values at all (variables+1) points of polynomial q
// from the values at particular (degree+1) points with q(x) = y
// Saving the degree of polynomial q in the variable "degree"
bool interpolateValidPolynomial(int& degree, int variables, int* x, int* y, int* q)
{
    int lagrangeNumerator[DEGREE + 1];
    int lagrangeBasisNumerator[DEGREE + 1];

    // Initialize the known points of q, and set -1 for the unknown points
    for (int i = 0; i <= variables; ++i) q[i] = -1;
    for (int i = 0; i <= degree; ++i) q[x[i]] = y[i];
    
    // Lagrange polynomial = (lN[0] + lN[1]x + lN[2]x^2 + ...) / lD
    int lagrangeDenominator = 1, lagrangeBasisDenominator;
    for (int i = 0; i <= degree; ++i) lagrangeNumerator[i] = 0;

    // Computing the Lagrange polynomial in integer numbers
    for (int j = 0; j <= degree; ++j)
    {
        lagrangeBasisDenominator = 1;
        for (int i = 0; i <= degree; ++i) lagrangeBasisNumerator[i] = 0;
        lagrangeBasisNumerator[0] = 1;

        int shift = 0;
        for (int m = 0; m <= degree; ++m)
        {
            if (m == j) continue;
            lagrangeBasisDenominator *= (x[j] - x[m]);
            for (int i = ++shift; i > 0; --i)
                lagrangeBasisNumerator[i] = lagrangeBasisNumerator[i] * (-x[m]) + lagrangeBasisNumerator[i - 1];
            lagrangeBasisNumerator[0] *= (-x[m]);
        }

        lagrangeBasisDenominator *= binom[variables][x[j]];
        int temporaryDenominator = lagrangeDenominator * (lagrangeBasisDenominator  / gcd(lagrangeDenominator, lagrangeBasisDenominator));
        for (int i = 0; i <= degree; ++i)
            lagrangeNumerator[i] = lagrangeNumerator[i] * (temporaryDenominator / lagrangeDenominator) + lagrangeBasisNumerator[i] * y[j] * (temporaryDenominator / lagrangeBasisDenominator);
        lagrangeDenominator = temporaryDenominator;
    }

    // Finding the real degree of the interpolated polynomial
    while (degree > 0 && lagrangeNumerator[degree] == 0) --degree;

    // Computing the values at the remaining points
    for (int i = 0; i <= variables; ++i)
    { 
        if (q[i] != -1) continue;
        long long powerOfBase = 1, result = 0;

        for (int j = 0; j <= degree; ++j)
        {
            result += powerOfBase * lagrangeNumerator[j];
            if (j != degree) powerOfBase = powerOfBase * i;
        }
        result *= binom[variables][i];
        if (result % lagrangeDenominator != 0) return false;
        result /= lagrangeDenominator;
        q[i] = (int) result;
    }

    return true;
}

// --------------------------------------------------------------------------------------------------------------------

// Check that all values of q are in the allowed range
bool validRangeOfValues(int variables, int* q, int minRangeCoef, int maxRangeCoef)
{
    for (int i = 0; i <= variables; ++i)
    {
        if (q[i] < minRangeCoef * binom[variables][i]) return false;
        if (q[i] > maxRangeCoef * binom[variables][i]) return false;
    }
    return true;
}

// --------------------------------------------------------------------------------------------------------------------

enum BinarySearchQualifier
{
    RIGHTMOST_ENTRY, // Find the largest entry which is less or equal to the one being searched
    EXACT_ENTRY, // Find the exact entry
    LEFTMOST_ENTRY // Find the least entry which is greater of equal to the one being searched
};

// Finds and element in poly between indices left and right, with a specific value at given position
int binarySearch(int left, int right, int position, int value, BinarySearchQualifier param)
{
#ifdef LIGHT_DEBUG_CODE
	if (param == EXACT_ENTRY)
	{
		printf("Error: binarySearch should never receive EXACT_ENTRY queries.\n");
		system("pause");
	}
#endif 
	// Check if the desired value is initially out of the range
	if (param == LEFTMOST_ENTRY && poly[right].q[position] < value) return -1;
	if (param == RIGHTMOST_ENTRY && poly[left].q[position] > value) return -1;

	while (left < right)
	{
        // L requires to find |.
        if (param == LEFTMOST_ENTRY)
        {
		    int middle = (left + right) / 2;
		    if (poly[middle].q[position] < value) left = middle + 1;
            else right = middle;
        }
        // R requires to find .|
        else if (param == RIGHTMOST_ENTRY)
        {
		    int middle = (left + right + 1) / 2;
		    if (poly[middle].q[position] > value) right = middle - 1;
            else left = middle;
        }
	}
#ifdef LIGHT_DEBUG_CODE
	if (left == right)
	{
		return left;
	} else {
        printf("Error: the binarySearch method did not stop in a correct state.\n");
        system("pause");
		return -1;
    }
#else
	return left;
#endif
}

// --------------------------------------------------------------------------------------------------------------------

// Finds a position in poly that satisfies the multiple passed requirements
// Returns -1 if there is no position satisfying the search parameter
int findIndex(int variables, int degree, int* index, int* value, BinarySearchQualifier param)
{
    int left = leftMostPolynomialIndex[variables], right = rightMostPolynomialIndex[variables];
	for (int i = 0; left <= right, i <= degree; ++i)
	{
		left = binarySearch(left, right, index[i], value[i], LEFTMOST_ENTRY);
		if (left == -1) return -1;
		right = binarySearch(left, right, index[i], value[i], RIGHTMOST_ENTRY);
		if (right == -1) return -1;
	}
    if (left > right) return -1; else
	if (param == RIGHTMOST_ENTRY)
		return right;
	else // EXACT or LEFTMOST_ENTRY
		return left;
}

// --------------------------------------------------------------------------------------------------------------------

// Get all possible ranges of saved polynomials whose values are between the boundaries set by minY and maxY
#ifdef WEIRD_OPTIMIZATION
queue<pair<int, int> > getRanges(int variables, int degree, int* index, int* minY, int* maxY)
#else
vector<pair<int, int> > getRanges(int variables, int degree, int* index, int* minY, int* maxY)
#endif
{
	// Create a container for storing all needed ranges
	queue<pair<int, int> > ranges;

	// Keep a number of elements that were stored in queue for any number of checked requirements (between 0 and degree, inclusive)
	int elements[DEGREE + 1];
	for (int i = 0; i < DEGREE + 1; ++i)
	{
		elements[i] = 0;
	}
	//vector<int> elements(degree + 1, 0);

	// Choose all polynomials with the requires number of variables as the initial range
	elements[0] = 1;
	ranges.push(make_pair(leftMostPolynomialIndex[variables], rightMostPolynomialIndex[variables]));

	// Check each of the requirements
	for (int i = 0; i <= degree; ++i)
	{
		// For each of the interval that satisfied all previous requirements
		for (int j = 0; j < elements[i]; ++j)
		{
			// Retrieve the current interval and delete it from the queue
			pair<int, int> currentRange = ranges.front();
			ranges.pop();

			// For the sake of efficiency, consider two cases
			if (i < degree)
			{
				// Split the current interval in many more intervals,
				// each satisfying one more (specific) condition for the value of y
				for (int y = minY[i]; y <= maxY[i]; ++y)
				{
					int left = currentRange.first;
					int right = currentRange.second;
					left = binarySearch(left, right, index[i], y, LEFTMOST_ENTRY);
					if (left == -1) continue;
					right = binarySearch(left, right, index[i], y, RIGHTMOST_ENTRY);
					if (right == -1 || left > right) continue;
					ranges.push(make_pair(left, right));
					++elements[i + 1];
				}
			} else {
				// Narrow the current interval to satisfy all y ranges between minY and maxY
				int left = currentRange.first;
				int right = currentRange.second;
				left = binarySearch(left, right, index[i], minY[i], LEFTMOST_ENTRY);
				if (left == -1) continue;
				right = binarySearch(left, right, index[i], maxY[i], RIGHTMOST_ENTRY);
				if (right == -1 || left > right) continue;
				ranges.push(make_pair(left, right));
			}
		}
	}

#ifdef WEIRD_OPTIMIZATION
	return ranges;
#else
	// TODO: understand this vector <-> queue change
	// Put the result into a vector
	vector<pair<int, int> > result;
	while (!ranges.empty())
	{
		result.push_back(ranges.front());
		ranges.pop();
	}
	return result;
#endif
}

// --------------------------------------------------------------------------------------------------------------------

// Given the candidate polynomial q, find the possible values in each point of q_0
// With a binary search find the range of positions in poly that satisfy these requirements
// For every q_0 in the range compute the (degree+1) points of q_1 and use a binary search
// to find whether it is in the list of valid polynomials
// If yes, save (q_0, q_1) as a valid decomposition
bool canSplitSymmetrizationPolynomial(SymmetrizationPolynomial& candidate)
{
    int x[DEGREE + 1], minY[DEGREE + 1], maxY[DEGREE + 1], z[DEGREE + 1];
    int degreeConditionContainer[2];

    int variables = candidate.variables - 1;
    int degree = min(DEGREE, variables);

    // Choose the points which define the left composite part of our polynomial
    initializeCombinations(degree, variables, x, NULL, NULL, NULL);
    // For each of these points find the minimum and maximum corresponding values of the left polynomial
    for (int i = 0; i <= degree; ++i)
    {
        int currentPolyValue = candidate.q[x[i]];
        if (x[i] == 0)
        {
            minY[i] = maxY[i] = currentPolyValue;
        } else {
            minY[i] = max(0, currentPolyValue  - binom[variables][x[i] - 1]);
            maxY[i] = min(binom[variables][x[i]], currentPolyValue);
        }
    }

	// Find the indices of the saved polynomials from "poly"
	// that are in the value range computed above
#ifdef WEIRD_OPTIMIZATION
	queue<pair<int, int> > ranges = getRanges(variables, degree, x, minY, maxY);
#else
	vector<pair<int, int> > ranges = getRanges(variables, degree, x, minY, maxY);
#endif
	
	// Process each of the final ranges
#ifdef WEIRD_OPTIMIZATION
	while (!ranges.empty())
	{
		pair<int, int> myRange = ranges.front();
		ranges.pop();
		for (int left = myRange.first; left <= myRange.second; ++left)
#else
	for (vector<pair<int, int> >::const_iterator it = ranges.begin(); it != ranges.end(); ++it)
	{
		for (int left = it->first; left <= it->second; ++left)
#endif
		{
			bool validDifference = true;
			// Computing the values of the right polynomial
			for (int j = 0; j <= degree; ++j)
			{
				z[j] = candidate.q[x[j] + 1];
				if (x[j] != variables)
					z[j] -= poly[left].q[x[j] + 1];
				if (z[j] < 0 || z[j] > binom[variables][x[j]])
				{
					// Compensating for the faulty binary search algorithm
					validDifference = false;
					break;
				}
			}
			if (!validDifference) continue;

			// Check if the right polynomial is in the list of all valid polynomials
			int right = findIndex(variables, degree, x, z, EXACT_ENTRY);
			if (right == -1) continue;

#ifdef HEAVY_DEBUG_CODE
			int minRightIndex = findIndex(variables, degree, x, z, LEFTMOST_ENTRY);
			int maxRightIndex = findIndex(variables, degree, x, z, RIGHTMOST_ENTRY);
			if (minRightIndex == -1 || minRightIndex == -1 || minRightIndex != maxRightIndex || right != maxRightIndex)
			{
				printf("Error: the exact-match binary search does not correspond to the individual \
					   leftmost-match and rightmost-match binary search results.\n");
				system("pause");
				continue;
			}
#endif

#ifdef LIGHT_DEBUG_CODE
			// Check that the sum of all entries of the left and right polynomials
			// matches the entries of the candidate polynomial
			bool validSplit = true;
			for (int j = 0; j < variables; ++j)
				if (candidate.q[j + 1] != poly[left].q[j + 1] + poly[right].q[j])
				{
					printf("Error: found a wrong way to split a polynomial.\n");
					system("pause");
				}
#endif

#ifdef CHECK_DEGREE_CONDITIONS
			// Check that deg(right - left) <= deg(candidate) - 1
			degreeConditionContainer[0] = left;
			degreeConditionContainer[1] = right;
			if (!satisfiesDegreeConditions(degreeConditionContainer, 1, candidate.degree - 1)) continue;
#endif

			// Save the indices of the valid split
			candidate.splitPosition.push_back(make_pair(left, right));
		}
	}
    if (candidate.splitPosition.empty()) return false;

    return true;
}

// --------------------------------------------------------------------------------------------------------------------

// Get the maximum degree amongst the two positions whose numbers are passed to the function
int getDegreeOfPair(const pair<int, int>& positionPair)
{
    return max(poly[positionPair.first].degree, poly[positionPair.second].degree);
}

// A comparison function for sorting decompositions based on their degrees
bool compareMaxDegreeOfPairs(const pair<int, int>& a, const pair<int, int>& b)
{
    return (getDegreeOfPair(a) < getDegreeOfPair(b));
}

template <size_t size_y>
int reduce_to_echelon_form(int equations, int variables, long long system_of_equations[][size_y])
{
	long long lcm, pivot_coef, row_coef;
	int rowEchelonSize = 0;
	for (int i = 0; i < variables; ++i)
	{
		// Find the first row in column i with non-zero value
		int pivot_row = rowEchelonSize;
		while (pivot_row < equations && system_of_equations[pivot_row][i] == 0)
			++pivot_row;
		// If the column contains only zeros, ignore this column
		if (pivot_row == equations) continue;
		// Reduce the remaining column values to 0
		for (int row = pivot_row + 1; row < equations; ++row)
		{
			if (system_of_equations[row][i] == 0) continue;
			lcm = (system_of_equations[row][i] * system_of_equations[pivot_row][i]) / 
				gcd(abs(system_of_equations[row][i]), abs(system_of_equations[pivot_row][i]));
			pivot_coef = lcm / system_of_equations[pivot_row][i];
			row_coef = lcm / system_of_equations[row][i];
			for (int column = i; column < variables + 1; ++column)
				system_of_equations[row][column] = system_of_equations[row][column] * row_coef - system_of_equations[pivot_row][column] * pivot_coef;
		}
		// Swap rows: "pivot_row" with "rowEchelonSize"
		for (int column = 0; column < variables + 1; ++column)
			swap(system_of_equations[pivot_row][column], system_of_equations[rowEchelonSize][column]);
		// Swap columns: "i" with "rowEchelonSize"
		for (int row = 0; row < equations; ++row)
			swap(system_of_equations[row][i], system_of_equations[row][rowEchelonSize]);
		// Increase the size of row echelon
		++rowEchelonSize;
		if (rowEchelonSize == equations) break;
	}
	return rowEchelonSize;
}

template <size_t size_y>
bool exists_integer_solution(int rowEchelonSize, int equations, int variables, long long system_of_equations[][size_y])
{
	// No solutions exist at all
    for (int equation = rowEchelonSize; equation < equations; ++equation)
        if (system_of_equations[equation][variables] != 0)
		{
			//printf("Gauss: no solutions exist.\n");
			return false;
		}
	// Try to deduce a unique solution
    static long long solution[2 * VARIABLES + 1];
    for (int equation = rowEchelonSize - 1; equation > - 1; --equation)
    {
		// Infinite number of solutions
        for (int variable = rowEchelonSize; variable < variables; ++variable)
            if (system_of_equations[equation][variable] != 0)
				return true;

        long long value = system_of_equations[equation][variables];
		// Deduce the values of all previous variables
        for (int variable = equation + 1; variable < rowEchelonSize; ++variable)
            value -= (system_of_equations[equation][variable] * solution[variable]);
		// No integer solutions exist
        if (value % system_of_equations[equation][equation] != 0)
		{
			//printf("Gauss: no integer solutions exist.\n");
			return false;
		}
		// Compute the value of the current variable
        solution[equation] = value / system_of_equations[equation][equation];
		// No positive integer solutions exist
        if (solution[equation] < 0)
		{
			//printf("Gauss: no positive integer solutions exist.\n");
			return false;
		}
    }
#ifdef HEAVY_DEBUG_CODE
	int zeros = 0;
	for (int i = 0; i < rowEchelonSize; ++i)
		if (solution[i] == 0)
			++zeros;
	zeros += variables - rowEchelonSize;
	if (zeros > 0)
	{
		// TODO: throw away such splits
		printf("Gauss: a positive integer solution found (%d unused splits).\n", zeros);
	}
#endif
	return true;
}

// A functions creates a system of equation based on the 1-st level decompositions of a candidate polynomial
// It finds all possible solutions and eliminates the decompositions that are never used in any of such solutions
bool canSolveSystemOfEquations(SymmetrizationPolynomial& candidate)
{
	// The array for storing the system of equations and transforming it into an echelon form
	static long long system_of_equations[2 * VARIABLES + 1][350000 + 1]; // TODO: max number of variables? For now 350'000
    int variables = candidate.splitPosition.size();
	int equations = 2 * candidate.variables + 1;

    // TODO: degree processing?
	// Sort all the decompositions in order of their maximum degree
    // sort(candidate.splitPosition.begin(), candidate.splitPosition.end(), compareMaxDegreeOfPairs);

    // Add the main equation that limits the sum of all variables in the system of equations
	for (int i = 0; i < variables; ++i) system_of_equations[0][i] = 1;
	system_of_equations[0][variables] = candidate.variables;
    // Add the equations for the case when a single variable is replaced by value 0
    for (int k = 0; k <= candidate.variables - 1; ++k)
    {
        int index = 0;
        for (vector<pair<int, int> >::iterator it = candidate.splitPosition.begin(); it != candidate.splitPosition.end(); ++it)
            system_of_equations[1 + k][index++] = poly[it->first].q[k];
        system_of_equations[1 + k][variables] = binom[candidate.variables - k][1] * candidate.q[k];
    }
    // Add the equations for the case when a single variable is replaced by value 1
    for (int k = 1; k <= candidate.variables; ++k)
    {
        int index = 0;
        for (vector<pair<int, int> >::iterator it = candidate.splitPosition.begin(); it != candidate.splitPosition.end(); ++it)
            system_of_equations[candidate.variables + k][index++] = poly[it->second].q[k - 1];
		system_of_equations[candidate.variables + k][variables] = binom[k][1] * candidate.q[k];
    }

	int rowEchelonSize = reduce_to_echelon_form(equations, variables, system_of_equations);

    // TODO: Check & change the degree of candidate depending on the involved splits

    return exists_integer_solution(rowEchelonSize, equations, variables, system_of_equations);
}

// ====================================================================================================================
// Check the degree conditions
// ====================================================================================================================

// Computes the expression (additions and subtractions) of polynomials and checks their degree
// This method uses static arrays because it greatly improves the speed performance
// P.S. Can optimize the efficiency twice, by passing one of the pre-computed sums
bool satisfiesDegreeConditions(int* container, int positionToTest, int maxAllowedDegree)
{
    static int index[DEGREE + 1], value[DEGREE + 1];
    int variables = poly[container[positionToTest]].variables;
	static int expressionResult[VARIABLES + 1]; // A vector to store the result of expression
	for (int i = 0; i < variables + 1; ++i)
	{
		expressionResult[i] = 0;
	}

    // Iterate through all the decomposition polynomials and compute the expression
    int bitsInIndex = countBits(positionToTest);
    for (int pos = 0; pos <= positionToTest; ++pos)
    {
        // Only continue if each of the bits of the current index is also included inside "index"
        if ((pos | positionToTest) != positionToTest) continue;

        // Find the coefficient of the current polynomial: 1 (add) or -1 (subtract)
        int bitNumberDifference = bitsInIndex - countBits(pos);
        // Compute the coefficient in the expression for the current polynomial
        int coefficient = - 1;
        if (bitNumberDifference % 2 == 0) coefficient = 1;

        // Add or subtract each of the terms
        for (int i = 0; i <= variables; ++i)
            expressionResult[i] = expressionResult[i] + coefficient * poly[container[pos]].q[i];
    }
    
    // If the maximum allowed degree is negative, it basically means that the resulting polynomial must be 0
    if (maxAllowedDegree < 0)
    {
        for (int i = 0; i <= variables; ++i)
            if (expressionResult[i] != 0) return false;
        return true;
    }

    // Initializing a list of positions with the least number of possible values
    initializeCombinations(maxAllowedDegree, variables, index, NULL, NULL, NULL);

    // Filling the values that correspond to the chosen indices
    for (int i = 0; i <= maxAllowedDegree; ++i) value[i] =  expressionResult[index[i]];

    // Create an array to store the interpolated values
	static int q[VARIABLES + 1];
    //int* q = new int[variables + 1];
    if (!interpolateValidPolynomial(/* by reference */ maxAllowedDegree, variables, index, value, /* by reference */ q))
    {
        return false;
    }

    // Check that all interpolated values match the result of the expression
    for (int i = 0; i <= variables; ++i)
        if (expressionResult[i] != q[i])
        {
            return false;
        }
    return true;
}

// ====================================================================================================================
// ====================================================================================================================

// Find and save all symmetrization polynomials on of size <= VARIABLES such that each of them can be divided in smaller parts
// The polynomials must satisfy the degree requirement and it should be possible to solve a system of equations.
// Hence each of them can be fully decomposed.
void initializeSymmetrizationPolynomials()
{
    // The points we use to interpolate a polynomial q   
    int index[DEGREE + 1], value[DEGREE + 1], minValue[DEGREE + 1], maxValue[DEGREE + 1];
    // The complete information about the polynomial q
    int q[VARIABLES + 1];

    // Adding the two cases of degree = 0 and variables = 0, i.e. the constants "0" and "1"
    int zero = 0, one = 1;
    poly.push_back(SymmetrizationPolynomial(/* degree */ 0, /* variable */ 0, &zero));
    poly.push_back(SymmetrizationPolynomial(/* degree */ 0, /* variable */ 0, &one));
    leftMostPolynomialIndex[0] = 0;
    rightMostPolynomialIndex[0] = 1;

#ifdef DEBUG_OUTPUT
    int interpolationAttempts = 0;
#endif

    // Adding the cases with variables > 0
    for (int variables = 1; variables <= VARIABLES; ++variables)
    {
#ifdef DEBUG_OUTPUT
		clock_t begin = clock();
#endif
        // Indicating that no symmetrization polynomials of this length were found (yet)
        rightMostPolynomialIndex[variables] = -1; 
        // Choosing (maxDegree + 1) points (out of "variable" points) with the least number of possible values
        int maxDegree = min(DEGREE, variables);
        initializeCombinations(maxDegree, variables, index, value, minValue, maxValue);
        // Generate all possible combinations of values at the selected (maxDegree + 1) points
        do
        {
#ifdef DEBUG_OUTPUT
            ++interpolationAttempts;
#endif
            // Interpolate the remaining (variables - maxDegree) points
            int degree = maxDegree;
            if (!interpolateValidPolynomial(/* by reference */ degree, variables, index, value, /* by reference */ q)) continue;
            // Check that all the resulting points are integers in the required range
            if (!validRangeOfValues(variables, q, /* minRangeCoef */ 0, /* maxRangeCoef */ 1)) continue;
            // Create the symmetrization polynomial object for further storage/processing
            SymmetrizationPolynomial candidate(degree, variables, q);

            // Split the symmetrization polynomial above in all possible combinations of two smaller polynomials,
            // while checking the degree conditions for each of them
            if (!canSplitSymmetrizationPolynomial(candidate)) continue;
#ifdef SOLVE_SYSTEM_OF_EQUATIONS
            // Solve the system to equations to determine whether the current polynomial should be discarded alltogether
            if (!canSolveSystemOfEquations(candidate)) continue;
#endif

            if (variables == VARIABLES && candidate.q[1] == SENSITIVITY || SENSITIVITY == -1)
            {
                // TODO: call the decomposition function
            }

            // The new symmetrization polynomial satsified all the conditions, so we save it			
			//candidate.splitPosition.clear(); // TODO:
            poly.push_back(candidate);
            if (rightMostPolynomialIndex[variables] == -1) leftMostPolynomialIndex[variables] = poly.size() - 1;
            rightMostPolynomialIndex[variables] = poly.size() - 1;
        }
        // Generate the next combination of values at the selected (degree + 1) points 
        while (generateNextCombination(maxDegree, value, minValue, maxValue));
#ifdef DEBUG_OUTPUT
		clock_t end = clock();
		double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
        printf("Saved %d of %d symmetrization polynomials on %d variables (%.2f seconds).\n", rightMostPolynomialIndex[variables] - leftMostPolynomialIndex[variables] + 1, interpolationAttempts, variables, elapsed_secs);
        interpolationAttempts = 0;
#endif
		/*
		vector<bool> valid(poly.size(), false);
		for (int v = variables; v > 0; --v)
		{
			for (int i = leftMostPolynomialIndex[v]; i <= rightMostPolynomialIndex[v]; ++i)
			{
				if (v == variables) valid[i] = true;
				if (!valid[i]) continue;
				for (int j = 0; j < poly[i].splitPosition.size(); ++j)
				{
					valid[poly[i].splitPosition[j].first] = true;
					valid[poly[i].splitPosition[j].second] = true;
				}
			}
		}
		for (int i = 0; i < poly.size(); ++i)
		{
			if (valid[i]) continue;
			poly[i].valid = false;
			poly[i].q.clear();
			poly[i].splitPosition.clear();
		}

		printf("The number of remaining valid polynomials:");
		for (int v = 0; v < variables; ++v)
		{
			int cnt = 0;
			for (int i = leftMostPolynomialIndex[v]; i <= rightMostPolynomialIndex[v]; ++i)
			{
				if (poly[i].valid) ++cnt;
			}
			printf(" %d", cnt);
			if (v != variables - 1) printf(",");
		}
		printf("\n");
		*/
    }
}

// ====================================================================================================================
// ====================================================================================================================

/*
class DecompositionLevel
{
public:
    DecompositionLevel() {} // TODO:
    ~DecompositionLevel() {} // TODO:
    int getDecompositionDepth() const { return decompositionDepth; }

private:
    int decompositionDepth; // `0' for an initial symmetrization polynomial, `1' for a 1-st level of decomposition, etc.
    int* parentDecompositionIDs; // Ordered array of decompositionDepth elements containing IDs of parent decompositions
    int decompositionPolynomials; // 2^(decompositionDepth) symmetrization polynomials
};

vector<int> processingOrder; // The order of splitting the symmetrization polynomials within a single level of decomposition
queue<DecompositionLevel> decompositionQueue; // The queue containing all the decomposition levels not processed further yet

// ====================================================================================================================
short currentSplit[1<<(VARIABLES-1)];
short totalSplits[1<<(VARIABLES-1)];
int currentSubsetSum[1<<VARIABLES];

void generateNextDecompositionLevel(const DecompositionLevel& decomp)
{

}
*/

int main()
{
    //printf("Initializing... ");
    initializeBinomialCoefficients(); // Initialize \binom{n}{k} for all 0 <= n, k <= VARIABLES
    initializeSymmetrizationPolynomials(); // Enumerate all symmetrization polynomials on <=VARIABLES that can be split in smaller parts
	
    printf("Done!\n");
    return 0;
/*    
    // TODO: generate all starting polynomials and put them in decompositionQueue and in initialSymmetrizationPolynomials

    for (int decompositionDepth = 0; decompositionDepth < VARIABLES; ++decompositionDepth)
    {
        // TODO: update the processingOrder
        if (decompositionQueue.empty()) break;
        while (decompositionQueue.front().getDecompositionDepth() == decompositionDepth)
        {
            // TODO: take the front decomposition level and generate every possible next decomposition level
            generateNextDecompositionLevel(decompositionQueue.front());
            // TODO: solve the system of equations involving the single old and all new decomposition levels
            decompositionQueue.pop();
        }
        // TODO: solve a bigger system of equations involving the initial symmetrization polynomial and all stored decomposition levels
    }

    printf("%d full decompositions found.\n", decompositionQueue.size());
    return 0;
	*/
}
