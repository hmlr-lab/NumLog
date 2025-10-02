#include <SWI-cpp2.h>
#include <vector>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <limits>
#include <string>
#include <map>
#include <set>
#include <unordered_set>
#

using namespace std;

// Calculate mean of a vector
double calculateMean(const vector<double>& data) {
    if (data.empty()) return 0.0;
    double sum = 0.0;
    for (double val : data) {
        sum += val;
    }
    return sum / data.size();
}

// Calculate standard deviation of a vector
double calculateStdDev(const vector<double>& data, double mean, double default_stddev) {
    if (data.empty()) return default_stddev;
    double variance = 0.0;
    for (double value : data) {
        variance += (value - mean) * (value - mean);
    }
    variance /= max(1.0, static_cast<double>(data.size()));
    double stddev = sqrt(variance);
    return max(stddev, default_stddev); // Ensure reasonable stddev
}

// Gaussian PDF
double gaussianPDF(double x, double mean, double stddev) {
    double coeff = 1.0 / (stddev * sqrt(2.0 * M_PI));
    double exponent = -0.5 * pow((x - mean) / stddev, 2);
    return coeff * exp(exponent);
}

// Numerical search for intersection using bisection
vector<double> findGaussianIntersections(double mean1, double stddev1, double mean2, double stddev2, double min_x, double max_x) {
    vector<double> intersections;

    // Define function: f(x) = pos_pdf(x) - neg_pdf(x)
    auto diff = [&](double x) {
        return gaussianPDF(x, mean1, stddev1) - gaussianPDF(x, mean2, stddev2);
    };

    // Bisection search in small intervals
    const int steps = 100;
    double step = (max_x - min_x) / steps;
    for (int i = 0; i < steps; ++i) {
        double x1 = min_x + i * step;
        double x2 = min_x + (i + 1) * step;
        double f1 = diff(x1);
        double f2 = diff(x2);

        if (f1 * f2 <= 0) { // Sign change indicates root
            // Bisection
            double left = x1;
            double right = x2;
            for (int iter = 0; iter < 50; ++iter) {
                double mid = (left + right) / 2.0;
                double f_mid = diff(mid);
                if (abs(f_mid) < 1e-6 || (right - left) < 1e-6) {
                    intersections.push_back(mid);
                    break;
                }
                if (f1 * f_mid <= 0) {
                    right = mid;
                } else {
                    left = mid;
                    f1 = f_mid;
                }
            }
        }
    }

    // Deduplicate and sort
    sort(intersections.begin(), intersections.end());
    intersections.erase(
        unique(intersections.begin(), intersections.end(),
               [](double a, double b) { return abs(a - b) < 1e-6; }),
        intersections.end());

    return intersections;
}

// Simple k-means clustering for initializing GMM components
vector<vector<double>> clusterData(const vector<double>& data, int k, double min_stddev) {
    if (data.empty() || k <= 0) return {};
    vector<double> sorted_data = data;
    sort(sorted_data.begin(), sorted_data.end());
    vector<vector<double>> clusters(k);

    // Initialize centroids
    vector<double> centroids(k);
    for (int i = 0; i < k; ++i) {
        centroids[i] = sorted_data[i * (sorted_data.size() - 1) / max(1, k - 1)];
    }

    // Assign points to nearest centroid
    for (double x : sorted_data) {
        int closest = 0;
        double min_dist = abs(x - centroids[0]);
        for (int i = 1; i < k; ++i) {
            double dist = abs(x - centroids[i]);
            if (dist < min_dist) {
                min_dist = dist;
                closest = i;
            }
        }
        clusters[closest].push_back(x);
    }

    // Ensure non-empty clusters
    vector<vector<double>> valid_clusters;
    for (auto& c : clusters) {
        if (!c.empty()) {
            valid_clusters.push_back(c);
        }
    }
    return valid_clusters.empty() ? vector<vector<double>>{data} : valid_clusters;
}

// Function to find thresholds using GMM
vector<double> find_thresholds(const vector<double>& pos, const vector<double>& neg) {
    vector<double> thresholds;

    // Check if data is sufficient
    if (pos.empty() && !neg.empty()) {
        thresholds.push_back(neg.front());
        thresholds.push_back(neg.back());
        //cout << "Error: Empty positive or negative data" << endl;
        return thresholds;
    }
    else if(!pos.empty() && neg.empty())
    {
        thresholds.push_back(pos.front());
        thresholds.push_back(pos.back());
        //cout << "Error: Empty positive or negative data" << endl;
        return thresholds;
    }
    else if(pos.empty() && neg.empty()){
         cout << "Error: Empty positive or negative data" << endl;
         return thresholds;
    }

    // Combine data to determine range
    vector<double> combined = pos;
    combined.insert(combined.end(), neg.begin(), neg.end());
    double min_x = *min_element(combined.begin(), combined.end());
    double max_x = *max_element(combined.begin(), combined.end());
    double data_range = max_x - min_x;
    double default_stddev = data_range / 10.0; // Reasonable stddev for small clusters

    // Cluster data (up to 2 components)
    int k = min(2, static_cast<int>(min(pos.size(), neg.size())));
    vector<vector<double>> pos_clusters = clusterData(pos, k, default_stddev);
    vector<vector<double>> neg_clusters = clusterData(neg, k, default_stddev);

    // Compute GMM parameters
    vector<double> pos_means, pos_stddevs, pos_weights;
    vector<double> neg_means, neg_stddevs, neg_weights;
    double total_pos = pos.size();
    double total_neg = neg.size();

    for (const auto& cluster : pos_clusters) {
        double mean = calculateMean(cluster);
        double stddev = calculateStdDev(cluster, mean, default_stddev);
        double weight = static_cast<double>(cluster.size()) / total_pos;
        pos_means.push_back(mean);
        pos_stddevs.push_back(stddev);
        pos_weights.push_back(weight);
        cout << "Pos cluster: mean = " << mean << ", stddev = " << stddev << ", weight = " << weight << endl;
    }

    for (const auto& cluster : neg_clusters) {
        double mean = calculateMean(cluster);
        double stddev = calculateStdDev(cluster, mean, default_stddev);
        double weight = static_cast<double>(cluster.size()) / total_neg;
        neg_means.push_back(mean);
        neg_stddevs.push_back(stddev);
        neg_weights.push_back(weight);
        cout << "Neg cluster: mean = " << mean << ", stddev = " << stddev << ", weight = " << weight << endl;
    }

    // Instead of intersections, just return empty thresholds
    return thresholds;
}
vector<string> convertToVectorString(term_t list) {
    vector<string> vec;
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(list);

    while (PL_get_list(tail, head, tail)) {
        char *str;

        // Try to convert term to a string (covers atoms, strings, numbers)
        if (PL_get_chars(head, &str, CVT_ALL | CVT_WRITE | BUF_DISCARDABLE)) {
            vec.emplace_back(str);
        } else {
            cerr << "Error: Cannot convert term to string!" << endl;
            return vec;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper list!" << endl;
    }

    return vec;
}
// Convert Prolog list to vector (unchanged)
vector<double> convertToVector(term_t list) {
    vector<double> vec;
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(list);

    while (PL_get_list(tail, head, tail)) {
        double value;
        if (PL_get_float(head, &value)) {
            vec.push_back(value);
        } else {
            cerr << "Error: Non-number value in list!" << endl;
            return vec;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper list!" << endl;
        return vec;
    }

    return vec;
}
// New function: Convert list of lists to vector<vector<double>>
vector<vector<double>> convertToVectorOfVectors(term_t listOfLists) {
    vector<vector<double>> result;
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(listOfLists);

    while (PL_get_list(tail, head, tail)) {
        // Each head is a sublist
        if (PL_is_list(head)) {
            result.push_back(convertToVector(head));
        } else {
            cerr << "Error: Expected a list inside outer list!" << endl;
            return result;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper outer list!" << endl;
    }

    return result;
}
// Convert vector to Prolog list (unchanged)
PlTerm convertToTerm(vector<double> vec) {
    term_t prolog_list = PL_new_term_ref();
    PL_put_nil(prolog_list);

    for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
        term_t head = PL_new_term_ref();
        PL_put_float(head, *it);
        PL_cons_list(prolog_list, head, prolog_list);
    }
    PlTerm pl_list(prolog_list);
    return pl_list;
}
PlTerm convertToTerm(vector<vector<double>> vec) {
    term_t outer_list = PL_new_term_ref();
    PL_put_nil(outer_list);

    // Iterate over the outer vector in reverse to maintain order in Prolog list
    for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
        // Create a Prolog list for the inner vector
        term_t inner_list = PL_new_term_ref();
        PL_put_nil(inner_list);

        // Iterate over the inner vector in reverse
        for (auto inner_it = it->rbegin(); inner_it != it->rend(); ++inner_it) {
            term_t head = PL_new_term_ref();
            PL_put_float(head, *inner_it);
            PL_cons_list(inner_list, head, inner_list);
        }

        // Add the inner list to the outer list
        term_t outer_head = PL_new_term_ref();
        PL_put_term(outer_head, inner_list);
        PL_cons_list(outer_list, outer_head, outer_list);
    }

    PlTerm pl_list(outer_list);
    return pl_list;
}

PlTerm convertToTerm(vector<vector<int>> vec) {
    term_t outer_list = PL_new_term_ref();
    PL_put_nil(outer_list);

    // Iterate over the outer vector in reverse to maintain order in Prolog list
    for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
        // Create a Prolog list for the inner vector
        term_t inner_list = PL_new_term_ref();
        PL_put_nil(inner_list);

        // Iterate over the inner vector in reverse
        for (auto inner_it = it->rbegin(); inner_it != it->rend(); ++inner_it) {
            term_t head = PL_new_term_ref();
            PL_put_integer(head, *inner_it);
            PL_cons_list(inner_list, head, inner_list);
        }

        // Add the inner list to the outer list
        term_t outer_head = PL_new_term_ref();
        PL_put_term(outer_head, inner_list);
        PL_cons_list(outer_list, outer_head, outer_list);
    }

    PlTerm pl_list(outer_list);
    return pl_list;
}

// Convert a vector<string> to a Prolog list of atoms
PlTerm convertVectorStringToTerm(const vector<string>& vec) {
    term_t list = PL_new_term_ref();       // Will hold the resulting list
    PL_put_nil(list);                      // Start with an empty list

    term_t elem = PL_new_term_ref();       // Temporary term for each element

    // Build list from back to front
    for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
        PL_put_atom_chars(elem, it->c_str());  // Convert string to Prolog atom
        PL_cons_list(list, elem, list);        // list = [elem | list]
    }
    PlTerm pl_list(list);
    return pl_list;
}

void binningData(vector<double> pos, vector<double> neg, vector<double> threshold, vector<double> &leq, vector<vector<double>> &inRange, vector<double> &geq) {

    vector<double> temp;
    vector<double> result;

    temp.insert(temp.end(), pos.begin(), pos.end());
    temp.insert(temp.end(), neg.begin(), neg.end());
    temp.insert(temp.end(), threshold.begin(), threshold.end());
    

    sort(temp.begin(), temp.end());


    vector<double> unique_temp;
    int check =0;
    for(auto& t:temp)
    {
            if(find(neg.begin(), neg.end(),t) == neg.end())
            {
                unique_temp.push_back(t);
            }
            else
            {
                if(leq.empty() && check ==0){
                    if(unique_temp.empty())check=1;
                    leq.insert(leq.begin(),unique_temp.begin(), unique_temp.end());
                  
                 }
                else if (!leq.empty() || check==1)
                    inRange.push_back(unique_temp);

                    unique_temp.clear();
            }
            
    }

        if(!unique_temp.empty())geq.insert(geq.end(), unique_temp.begin(), unique_temp.end());

}

// Prolog predicate
PREDICATE(findThresholds, 4) {
    term_t pos_term = A1.unwrap();
    term_t neg_term = A2.unwrap();

    vector<double> pos = convertToVector(pos_term);
    vector<double> neg = convertToVector(neg_term);

    // Combine data to determine range
    vector<double> combined = pos;
    combined.insert(combined.end(), neg.begin(), neg.end());
    double min_x = *min_element(combined.begin(), combined.end());
    double max_x = *max_element(combined.begin(), combined.end());
    double data_range = max_x - min_x;
    double default_stddev = data_range / 10.0; // Reasonable stddev for small clusters

    // Cluster data (up to 2 components)
    int k = min(2, static_cast<int>(min(pos.size(), neg.size())));
    vector<vector<double>> pos_clusters = clusterData(pos, k, default_stddev);
    vector<vector<double>> neg_clusters = clusterData(neg, k, default_stddev);

    

    vector<vector<double>> negClusters;
    for (const auto& cluster : neg_clusters) {
        double mean = calculateMean(cluster);
        double stddev = calculateStdDev(cluster, mean, default_stddev);
        negClusters.push_back({mean, stddev});
    }

    vector<vector<double>> posClusters;
    for (const auto& cluster : pos_clusters) {
        double mean = calculateMean(cluster);
        double stddev = calculateStdDev(cluster, mean, default_stddev);
        // Check if this mean/stddev pair exists in negClusters
        bool found = false;
        for (const auto& nc : negClusters) {
            if (std::abs(nc[0] - mean) < 1e-6 && std::abs(nc[1] - stddev) < 1e-6) {
                found = true;
                break;
            }
        }
        if (!found) posClusters.push_back({mean, stddev});
    }
    // Convert to Prolog list and unify
    A3.unify_term(convertToTerm(posClusters));
    A4.unify_term(convertToTerm(negClusters));

    return true;
}
////////////////////////////////////Relations//////////////////////

// Compare function to determine relation between two sets
string compareSets(const vector<double>& a, const vector<double>& b) {
    bool allLess = true, allGreater = true, allEqual = true;

    for (int x : a) {
        for (int y : b) {
            if (x >= y) allLess = false;
            if (x <= y) allGreater = false;
            if (x != y) allEqual = false;
        }
    }

    if (allEqual) return "=";
    else if (allLess) return "<";
    else if (allGreater) return ">";
    else return "?"; // ambiguous or overlapping
}

// Attempt to build a totally ordered chain
vector<string> findOrderedSubset(map<string, vector<double>>& datasets) {
    vector<string> keys;
    for (const auto& [k, _] : datasets) keys.push_back(k);

    vector<string> bestChain;

    // Try all subsets
    size_t n = keys.size();
    for (size_t mask = 1; mask < (1 << n); ++mask) {
        vector<string> subset;
        for (size_t i = 0; i < n; ++i)
            if (mask & (1 << i)) subset.push_back(keys[i]);

        bool valid = true;
        for (size_t i = 0; i < subset.size(); ++i) {
            for (size_t j = i + 1; j < subset.size(); ++j) {
                string r = compareSets(datasets[subset[i]], datasets[subset[j]]);
                if (r == "?") {
                    valid = false;
                    break;
                }
            }
            if (!valid) break;
        }

        if (valid && subset.size() > bestChain.size())
            bestChain = subset;
    }

    // Sort the bestChain using `<` relation
    sort(bestChain.begin(), bestChain.end(), [&](const string& a, const string& b) {
        return compareSets(datasets[a], datasets[b]) == "<";
    });

    return bestChain;
}


PREDICATE(findRelations, 3){

    term_t pred_names = A1.unwrap();
    term_t pred_values = A2.unwrap();

    vector<string> terms = convertToVectorString(pred_names);
    vector<vector<double>> values = convertToVectorOfVectors(pred_values);

    map<string, vector<double>> datasets;

    for(int i=0;i<terms.size();i++)
    {
        datasets[terms[i]] = values[i];
    }
   

    vector<string> chain = findOrderedSubset(datasets);

    // Report excluded datasets
    set<string> chainSet(chain.begin(), chain.end());
    for (const auto& [k, _] : datasets) {
        if (!chainSet.count(k))
            cout << "Excluding dataset " << k << " due to ambiguous relation.\n";
    }

    // Output relation
    vector<string> results;
    //cout << "Valid ordering:\n";
    if (!chain.empty()) {
        //cout << chain[0];
        results.push_back(chain[0]);
        for (size_t i = 1; i < chain.size(); ++i) {
            //cout << " < " << chain[i];
            results.push_back(chain[i]);
        }
        //cout << endl;
    } //else {
       // cout << "No valid ordering.\n";
    //}
    A3.unify_term(convertVectorStringToTerm(results));
    return true;
}

////////////Combinations///////////////////
// Helper function to print a combination


// Recursive function to generate combinations up to max length
void generateCombinations(const vector<int>& input, vector<int>& current, int index, int maxLen, vector<vector<int>>& result) {
    for (int i = index; i < input.size(); ++i) {
        current.push_back(input[i]);

        if (current.size() <= maxLen) {
             result.push_back(current); 
            generateCombinations(input, current, i + 1, maxLen,result); // only go deeper if size <= maxLen
        }

        current.pop_back(); // backtrack
    }
}


PREDICATE(combinations, 3){
    int count = (int) A1;
    int max = (int) A2;
    vector<int> input;
    for(int i=1;i<count;i++)
    {
       input.push_back(i);
    }

    vector<int> current;
    vector<vector<int>> result;
    // Sort input to ensure consistency (not strictly needed for ints but useful in general)
    //sort(input.begin(), input.end());
    generateCombinations(input, current, 0,max,result);

    A3.unify_term(convertToTerm(result));
    
    return true;
}

//////////////////////Find the best Rules//////////////////////

struct Rule {
    std::string name;
    std::unordered_set<std::string> positives;
    std::unordered_set<std::string> negatives;
    term_t gmm;
    term_t relations;
};

// Returns true if the rule covers any negative example
bool coversNegative(const Rule& rule) {
    return !rule.negatives.empty();
}

// Computes how many positives from allPos are covered by the rule
int countPositivesCovered(const Rule& rule, const std::unordered_set<std::string>& allPos) {
    int count = 0;
    for (const auto& p : rule.positives) {
        if (allPos.count(p)) count++;
    }
    return count;
}


void convertToVectorString(term_t list,vector<string> &vecList) {
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(list);

    while (PL_get_list(tail, head, tail)) {
        char* str;
        if (PL_get_chars(head, &str, CVT_ALL | CVT_WRITE | BUF_DISCARDABLE | REP_UTF8)) {
            if (find(vecList.begin(), vecList.end(), str) == vecList.end()) {
                vecList.push_back(str);
                } 
          
        } else {
            cerr << "Error: Cannot convert element to string!" << endl;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper list structure!" << endl;
    }

  
}


vector<string> gmmList;
vector<string> relationsList;
// Returns all rules that cover positives and no negatives
std::vector<std::string> selectBestRules(const std::vector<Rule>& rules, const std::unordered_set<std::string>& allPos) {
    std::vector<std::pair<int, Rule>> scored;

    for (const auto& rule : rules) {
        if (!coversNegative(rule)) {
            int coveredCount = countPositivesCovered(rule, allPos);
            if (coveredCount > 0) {
                scored.emplace_back(coveredCount, rule);
            }
        }
    }

    // Sort by number of positives covered (descending)
    std::sort(scored.begin(), scored.end(), [](const auto& a, const auto& b) {
        return a.first > b.first;
    });

    // Collect rule names
    std::vector<std::string> bestRules;
    std::unordered_set<std::string> alreadyCovered;

    for (const auto& [count, rule] : scored) {
        bool addsNew = false;
        for (const auto& p : rule.positives) {
            if (allPos.count(p) && !alreadyCovered.count(p)) {
                addsNew = true;
                alreadyCovered.insert(p);
            }
        }
        if (addsNew) {
            bestRules.push_back(rule.name);
            convertToVectorString(rule.gmm, gmmList);
            convertToVectorString(rule.relations, relationsList);
            //cout << "Selected rule: " << rule.name << " with " << count << " positives covered." << endl;
        }
    }

    return bestRules;
}
unordered_set<string> convertToSetString(term_t list) {
    unordered_set<string> result;
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(list);

    while (PL_get_list(tail, head, tail)) {
        char* str;
        if (PL_get_chars(head, &str, CVT_ALL | CVT_WRITE | BUF_DISCARDABLE)) {
            result.emplace(str);
        } else {
            cerr << "Error: Cannot convert element to string!" << endl;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper list structure!" << endl;
    }

    return result;
}


vector<Rule> convertToVectorRules(term_t list) {
    vector<Rule> rules;
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(list);

    while (PL_get_list(tail, head, tail)) {
        term_t nameTerm = PL_new_term_ref();
        term_t posListTerm = PL_new_term_ref();
        term_t negListTerm = PL_new_term_ref();
        term_t gmm = PL_new_term_ref();
        term_t relations = PL_new_term_ref();
        
        // Ensure it's a compound term: rule(Name, PosList, NegList)
        if (PL_get_arg(1, head, nameTerm) &&
            PL_get_arg(2, head, posListTerm) &&
            PL_get_arg(3, head, negListTerm) &&
            PL_get_arg(4, head, gmm) &&
            PL_get_arg(5, head, relations)) {
            
            char* nameStr;
            if (!PL_get_chars(nameTerm, &nameStr, CVT_ALL | CVT_WRITE | BUF_DISCARDABLE)) {
                cerr << "Error: Cannot convert rule name to string!" << endl;
                continue;
            }

            unordered_set<string> posSet = convertToSetString(posListTerm);
            unordered_set<string> negSet = convertToSetString(negListTerm);
            
          

            rules.push_back(Rule{nameStr, posSet, negSet,gmm,relations});

        


        } else {
            cerr << "Error: Invalid rule structure!" << endl;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper list structure!" << endl;
    }

    return rules;
}

PREDICATE(findBestRules, 2){
    // std::vector<Rule> rules = {
    //     {"r1", {"pos1"}, {"pos2"}},
    //     {"r2", {"pos3"}, {"neg1"}},
    //     {"r3", {"pos3"}, {}}
    // };
    term_t prolog_rules = A1.unwrap();
    vector<Rule> rules = convertToVectorRules(prolog_rules);
    term_t prolog_poses = A2.unwrap();
    //std::unordered_set<std::string> allPos = {"pos1", "pos2", "pos3"};
    std::unordered_set<std::string> allPos = convertToSetString(prolog_poses);

    auto best = selectBestRules(rules, allPos);

    std::cout << "\n\%--------------All Invented functions: "<<endl;
    for (const auto& r : gmmList) {
        std::cout << r <<"."<<endl;
    }
    std::cout << "\n\%--------------Relations: "<<endl;
    for (const auto& r : relationsList) {
        std::cout << r <<"."<<endl;
    }


    std::cout << "\n\%--------------Selected best rules: "<<endl;
    for (const auto& r : best) {
        std::cout << r <<"."<<endl;
    }
        // For each best rule, extract body predicates and match with gmm heads
        std::unordered_set<std::string> matchedGMMs;
        for (const auto& ruleStr : best) {
            // Extract body predicates from rule string (e.g., person(A):-hight(A).)
            size_t bodyStart = ruleStr.find("::-") != std::string::npos ? ruleStr.find("::-") + 3 : ruleStr.find(":-") + 2;
            if (bodyStart == std::string::npos) continue;
            std::string body = ruleStr.substr(bodyStart);
            // Split body by ',' and ';'
            std::vector<std::string> bodyPreds;
            size_t pos = 0;
            while (pos < body.size()) {
                size_t next = body.find_first_of(",;.", pos);
                std::string pred = body.substr(pos, next-pos);
                // Remove whitespace
                pred.erase(std::remove_if(pred.begin(), pred.end(), ::isspace), pred.end());
                if (!pred.empty()) bodyPreds.push_back(pred);
                if (next == std::string::npos) break;
                pos = next + 1;
            }
            // For each gmm, check if its head predicate name matches any body predicate name
            for (const auto& gmm : gmmList) {
                // Extract predicate name of gmm head (before '(' or ':-')
                size_t headEnd = gmm.find('(');
                if (headEnd == std::string::npos) headEnd = gmm.find(":-");
                std::string gmmHead = (headEnd != std::string::npos) ? gmm.substr(0, headEnd) : gmm;
                gmmHead.erase(std::remove_if(gmmHead.begin(), gmmHead.end(), ::isspace), gmmHead.end());
                // If gmmHead contains arguments, strip them
                size_t gmmNameEnd = gmmHead.find('(');
                std::string gmmName = (gmmNameEnd != std::string::npos) ? gmmHead.substr(0, gmmNameEnd) : gmmHead;
                for (const auto& bodyPred : bodyPreds) {
                    // Extract predicate name of body (before '(')
                    size_t bpEnd = bodyPred.find('(');
                    std::string bpName = (bpEnd != std::string::npos) ? bodyPred.substr(0, bpEnd) : bodyPred;
                    if (bpName == gmmName) {
                        matchedGMMs.insert(gmm);
                    }
                }
            }
        }
        for (const auto& gmm : matchedGMMs) {
            std::cout << gmm << "." << endl;
        }
    std::cout << std::endl;

    std::cout << std::endl;

    return true;
}
