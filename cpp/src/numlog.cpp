#include <SWI-cpp2.h>
#include <vector>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <limits>
#include <string>
#include <map>
#include <set>
#include <numeric>
#include <unordered_set>
#include <fstream>


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

// Fit a one-dimensional Gaussian mixture directly from the supplied samples.
vector<vector<double>> fitGaussianMixture(const vector<double>& data, int components) {
    if (data.empty() || components <= 0) return {};

    vector<double> sorted_data = data;
    sort(sorted_data.begin(), sorted_data.end());

    double data_mean = calculateMean(data);
    double data_variance = 0.0;
    for (double value : data) {
        data_variance += (value - data_mean) * (value - data_mean);
    }
    data_variance /= data.size();

    double data_range = sorted_data.back() - sorted_data.front();
    double min_stddev = max({1e-9, data_range * 1e-6, abs(data_mean) * 1e-12});
    double min_variance = min_stddev * min_stddev;

    vector<double> means(components);
    vector<double> variances(components, max(data_variance, min_variance));
    vector<double> weights(components, 1.0 / components);
    for (int i = 0; i < components; ++i) {
        size_t index = static_cast<size_t>(i) * (sorted_data.size() - 1) /
                       max(1, components - 1);
        means[i] = sorted_data[index];
    }

    const int max_iterations = 100;
    for (int iteration = 0; iteration < max_iterations; ++iteration) {
        vector<double> effective_counts(components, 0.0);
        vector<double> weighted_sums(components, 0.0);
        vector<double> responsibilities(components);

        for (double value : data) {
            double max_log_probability = -numeric_limits<double>::infinity();
            for (int i = 0; i < components; ++i) {
                double difference = value - means[i];
                responsibilities[i] = log(max(weights[i], 1e-15)) -
                    0.5 * log(2.0 * M_PI * variances[i]) -
                    difference * difference / (2.0 * variances[i]);
                max_log_probability = max(max_log_probability, responsibilities[i]);
            }

            double probability_sum = 0.0;
            for (double& responsibility : responsibilities) {
                responsibility = exp(responsibility - max_log_probability);
                probability_sum += responsibility;
            }
            for (int i = 0; i < components; ++i) {
                double responsibility = responsibilities[i] / probability_sum;
                effective_counts[i] += responsibility;
                weighted_sums[i] += responsibility * value;
            }
        }

        vector<double> new_means = means;
        vector<double> new_variances(components, 0.0);
        vector<double> new_weights(components);
        for (int i = 0; i < components; ++i) {
            if (effective_counts[i] > 1e-12) {
                new_means[i] = weighted_sums[i] / effective_counts[i];
                new_weights[i] = effective_counts[i] / data.size();
            } else {
                new_weights[i] = 1e-12;
            }
        }

        for (double value : data) {
            double max_log_probability = -numeric_limits<double>::infinity();
            for (int i = 0; i < components; ++i) {
                double difference = value - means[i];
                responsibilities[i] = log(max(weights[i], 1e-15)) -
                    0.5 * log(2.0 * M_PI * variances[i]) -
                    difference * difference / (2.0 * variances[i]);
                max_log_probability = max(max_log_probability, responsibilities[i]);
            }
            double probability_sum = 0.0;
            for (double& responsibility : responsibilities) {
                responsibility = exp(responsibility - max_log_probability);
                probability_sum += responsibility;
            }
            for (int i = 0; i < components; ++i) {
                double responsibility = responsibilities[i] / probability_sum;
                double difference = value - new_means[i];
                new_variances[i] += responsibility * difference * difference;
            }
        }
        for (int i = 0; i < components; ++i) {
            if (effective_counts[i] > 1e-12) {
                new_variances[i] = max(min_variance,
                    new_variances[i] / effective_counts[i]);
            } else {
                new_variances[i] = variances[i];
            }
        }

        double weight_sum = accumulate(new_weights.begin(), new_weights.end(), 0.0);
        for (double& weight : new_weights) {
            weight /= weight_sum;
        }

        double max_change = 0.0;
        for (int i = 0; i < components; ++i) {
            max_change = max(max_change, abs(new_means[i] - means[i]));
            means[i] = new_means[i];
            variances[i] = new_variances[i];
            weights[i] = new_weights[i];
        }
        if (max_change < 1e-8) break;
    }

    vector<vector<double>> mixture;
    for (int i = 0; i < components; ++i) {
        mixture.push_back({means[i], sqrt(variances[i]), weights[i]});
    }
    return mixture;
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

// Prolog predicate
PREDICATE(findThresholds, 4) {
    term_t pos_term = A1.unwrap();
    term_t neg_term = A2.unwrap();

    vector<double> pos = convertToVector(pos_term);
    vector<double> neg = convertToVector(neg_term);
    if (pos.empty() || neg.empty()) {
        return false;
    }

    // Fit up to two components per class, using the original values directly.
    int k = min(2, static_cast<int>(min(pos.size(), neg.size())));
    vector<vector<double>> pos_mixture = fitGaussianMixture(pos, k);
    vector<vector<double>> neg_mixture = fitGaussianMixture(neg, k);

    return A3.unify_term(convertToTerm(pos_mixture)) &&
           A4.unify_term(convertToTerm(neg_mixture));
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

    // Exclude ambiguous check: just return all keys
    return keys;
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
            cout << "Excluding feature " << k << " due to ambiguous relation.\n";
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
// Compute rule quality: higher = better
double computeRuleScore(const Rule& r, const unordered_set<string>& allPos) {
    int posCovered = countPositivesCovered(r, allPos);
    int negCovered = static_cast<int>(r.negatives.size());
    if (posCovered == 0) return 0.0;

    // Precision-like metric: penalize negatives
    double precision = static_cast<double>(posCovered) / (posCovered + negCovered + 1e-6);
    return precision;
}

// Select multiple high-precision rules that together cover more positives
std::vector<std::string> selectBestRules2(const std::vector<Rule>& rules,
                                         const std::unordered_set<std::string>& allPos,
                                         double precisionThreshold = 0.7) {
    // Clear globals for each run
    gmmList.clear();
    relationsList.clear();

    struct ScoredRule {
        double score;
        const Rule* rule;
    };

    std::vector<ScoredRule> scored;
    for (const auto& rule : rules) {
        double score = computeRuleScore(rule, allPos);
        if (score > 0.0) {
            scored.push_back({score, &rule});
        }
    }

    // Sort descending by score
    std::sort(scored.begin(), scored.end(),
              [](const ScoredRule& a, const ScoredRule& b) {
                  return a.score > b.score;
              });

    std::unordered_set<std::string> coveredPos;
    std::vector<std::string> bestRules;
    double cumulativePrecision = 1.0; // start with perfect

    for (const auto& sr : scored) {
        const Rule& rule = *sr.rule;

        // Calculate how many new positives this rule adds
        int newCovers = 0;
        for (const auto& p : rule.positives) {
            if (allPos.count(p) && !coveredPos.count(p))
                newCovers++;
        }

        if (newCovers == 0) continue; // skip redundant rules

        // Temporary union to compute new precision
        int totalPosCovered = static_cast<int>(coveredPos.size()) + newCovers;
        int totalNegCovered = 0;
        for (const auto& r2 : bestRules) {
            // You can maintain negatives if needed; for simplicity, ignore overlap
        }
        totalNegCovered += static_cast<int>(rule.negatives.size());

        double newPrecision =
            static_cast<double>(totalPosCovered) /
            (totalPosCovered + totalNegCovered + 1e-6);

        // Only accept if it doesn’t drop below threshold
        if (newPrecision >= precisionThreshold) {
            bestRules.push_back(rule.name);
            for (const auto& p : rule.positives)
                if (allPos.count(p)) coveredPos.insert(p);

            convertToVectorString(rule.gmm, gmmList);
            convertToVectorString(rule.relations, relationsList);

            cumulativePrecision = newPrecision;
            
        } 
    }

    std::cout << "Final precision: " << cumulativePrecision
              << " | Total covered positives: " << coveredPos.size() << std::endl;

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

PREDICATE(findBestRules, 3){
    // std::vector<Rule> rules = {
    //     {"r1", {"pos1"}, {"pos2"}},
    //     {"r2", {"pos3"}, {"neg1"}},
    //     {"r3", {"pos3"}, {}}
    // };
    term_t prolog_rules = A1.unwrap();
    vector<Rule> rules = convertToVectorRules(prolog_rules);
    // std::cout << rules.size() << " rules converted\n";
    // for(auto &r : rules) std::cout << r.name << std::endl;
    term_t prolog_poses = A2.unwrap();

    float threshold =  A3.as_float();
    //std::unordered_set<std::string> allPos = {"pos1", "pos2", "pos3"};
    std::unordered_set<std::string> allPos = convertToSetString(prolog_poses);
    auto best = vector<string>{};
    if(threshold==0.0) best = selectBestRules(rules, allPos);
    else best = selectBestRules2(rules, allPos, threshold); 

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

    std::ofstream ruleFile("rule.pl", std::ios::out | std::ios::trunc);
    if (ruleFile.is_open()) {
        for (const auto& r : best) {
            ruleFile << r << "." << std::endl;
        }
        for (const auto& r : gmmList) {
            ruleFile << r << "." << std::endl;
        }
        for (const auto& r : relationsList) {
            ruleFile << r << "." << std::endl;
        }
        ruleFile.close();
    } else {
        std::cerr << "Error: Unable to write rule.pl" << std::endl;
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


    return true;
}
