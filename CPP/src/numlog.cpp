#include <SWI-cpp2.h>
#include <vector>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <limits>
#include <string>
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

    // Compute intersections for all cluster pairs
    vector<double> candidate_thresholds;
    for (size_t i = 0; i < pos_means.size(); ++i) {
        for (size_t j = 0; j < neg_means.size(); ++j) {
            double search_min = min(pos_means[i], neg_means[j]) - 2 * max(pos_stddevs[i], neg_stddevs[j]);
            double search_max = max(pos_means[i], neg_means[j]) + 2 * max(pos_stddevs[i], neg_stddevs[j]);
            search_min = max(search_min, min_x);
            search_max = min(search_max, max_x);
            auto intersections = findGaussianIntersections(
                pos_means[i], pos_stddevs[i], neg_means[j], neg_stddevs[j], search_min, search_max);
            candidate_thresholds.insert(candidate_thresholds.end(), intersections.begin(), intersections.end());
        }
    }

    // Sort and deduplicate
    sort(candidate_thresholds.begin(), candidate_thresholds.end());
    candidate_thresholds.erase(
        unique(candidate_thresholds.begin(), candidate_thresholds.end(),
               [](double a, double b) { return abs(a - b) < 1e-6; }),
        candidate_thresholds.end());

    // Filter thresholds based on class transitions
    vector<double> sorted_pos = pos;
    vector<double> sorted_neg = neg;
    sort(sorted_pos.begin(), sorted_pos.end());
    sort(sorted_neg.begin(), sorted_neg.end());
    vector<double> sorted_combined = combined;
    sort(sorted_combined.begin(), sorted_combined.end());

    for (double t : candidate_thresholds) {
        for (size_t i = 0; i < sorted_combined.size() - 1; ++i) {
            double x1 = sorted_combined[i];
            double x2 = sorted_combined[i + 1];
            if (t > x1 && t < x2) {
                bool x1_is_pos = find(sorted_pos.begin(), sorted_pos.end(), x1) != sorted_pos.end();
                bool x2_is_pos = find(sorted_pos.begin(), sorted_pos.end(), x2) != sorted_pos.end();
                if (x1_is_pos != x2_is_pos) {
                    thresholds.push_back(t);
                   // cout << "Threshold at: " << t << endl;
                }
            }
        }
    }

    // Ensure all transitions are captured
    vector<double> unique_thresholds(thresholds.begin(), thresholds.end());
    thresholds.clear();
    thresholds.insert(thresholds.end(), unique_thresholds.begin(), unique_thresholds.end());

    // Check for missing transitions and add GMM-based or midpoint thresholds
    vector<pair<double, bool>> labeled_data;
    for (double p : pos) labeled_data.emplace_back(p, true);
    for (double n : neg) labeled_data.emplace_back(n, false);
    sort(labeled_data.begin(), labeled_data.end());

    for (size_t i = 0; i < labeled_data.size() - 1; ++i) {
        double x1 = labeled_data[i].first;
        double x2 = labeled_data[i + 1].first;
        bool class1 = labeled_data[i].second;
        bool class2 = labeled_data[i + 1].second;
        if (class1 != class2) {
            // Check if a threshold exists between x1 and x2
            bool has_threshold = false;
            double candidate_t = -1;
            for (double t : thresholds) {
                if (t > x1 && t < x2) {
                    has_threshold = true;
                    break;
                }
            }
            if (!has_threshold) {
                // Compute GMM-based threshold in this interval
                auto diff = [&](double x) {
                    double pos_pdf = 0.0;
                    double neg_pdf = 0.0;
                    for (size_t p = 0; p < pos_means.size(); ++p) {
                        pos_pdf += pos_weights[p] * gaussianPDF(x, pos_means[p], pos_stddevs[p]);
                    }
                    for (size_t n = 0; n < neg_means.size(); ++n) {
                        neg_pdf += neg_weights[n] * gaussianPDF(x, neg_means[n], neg_stddevs[n]);
                    }
                    return pos_pdf - neg_pdf;
                };
                double left = x1;
                double right = x2;
                double f1 = diff(left);
                double f2 = diff(right);
                if (f1 * f2 <= 0) {
                    for (int iter = 0; iter < 50; ++iter) {
                        double mid = (left + right) / 2.0;
                        double f_mid = diff(mid);
                        if (abs(f_mid) < 1e-6 || (right - left) < 1e-6) {
                            candidate_t = mid;
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
                if (candidate_t > x1 && candidate_t < x2) {
                    thresholds.push_back(candidate_t);
                   // cout << "Additional GMM threshold at: " << candidate_t << endl;
                } else {
                    // Fallback to midpoint
                    candidate_t = (x1 + x2) / 2.0;
                    thresholds.push_back(candidate_t);
                    //cout << "Fallback threshold at: " << candidate_t << endl;
                }
            }
        }
    }

    // Final sort
    sort(thresholds.begin(), thresholds.end());

    return thresholds;
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
PREDICATE(findThresholds, 5) {
    term_t pos_term = A1.unwrap();
    term_t neg_term = A2.unwrap();

    vector<double> pos = convertToVector(pos_term);
    vector<double> neg = convertToVector(neg_term);

    // Debug: Print input
    //cout << "Pos: ";
    //for (double p : pos) cout << p << " ";
    //cout << "\nNeg: ";
    //for (double n : neg) cout << n << " ";
    //cout << endl;

    // Find thresholds
    vector<double> thresholds = find_thresholds(pos, neg);

    // Print thresholds
    //for (auto& threshold : thresholds) {
     //   cout << "Final Threshold: " << threshold << endl;
    //}
    vector<double> leq;
    vector<double> geq;
    vector<vector<double>> inRange;
    
    binningData(pos, neg, thresholds, leq, inRange, geq);

    // Convert to Prolog list and unify
    
    
    A3.unify_term(convertToTerm(leq));
    A4.unify_term(convertToTerm(inRange));
    A5.unify_term(convertToTerm(geq));

    return true;
}