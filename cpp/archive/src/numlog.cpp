#include <iostream>
#include <vector>
#include <fstream>
#include <sstream>
#include <cmath>
#include <cstdlib>
#include <SWI-cpp2.h>


using namespace std;

// Sigmoid function
double sigmoid(double z) {
    return 1.0 / (1.0 + exp(-z));
}

// Compute prediction
double predict(const vector<double>& X, const vector<double>& weights, double bias) {
    double z = bias;
    for (size_t i = 0; i < X.size(); i++) {
        z += weights[i] * X[i];
    }
    return sigmoid(z);
}

// Train Logistic Regression using Gradient Descent with Class Weight Adjustment
void trainLogisticRegression(vector<vector<double>> X, vector<int> y, vector<double>& weights, double& bias, double lr, int epochs, double weight_pos, double weight_neg) {
    int m = X.size(); // Number of samples
    int n = X[0].size(); // Number of features

    // Initialize weights and bias
    weights.assign(n, 0.0);
    bias = 0.0;

    // Gradient Descent
    for (int epoch = 0; epoch < epochs; epoch++) {
        vector<double> gradient_w(n, 0.0);
        double gradient_b = 0.0;

        // Compute gradients
        for (int i = 0; i < m; i++) {
            double pred = predict(X[i], weights, bias);
            double error = pred - y[i];

            // Assign weight based on class
            double sample_weight = (y[i] == 1) ? weight_pos : weight_neg;

            // Compute weighted gradients
            for (int j = 0; j < n; j++) {
                gradient_w[j] += sample_weight * error * X[i][j];
            }
            gradient_b += sample_weight * error;
        }

        // Update weights and bias
        for (int j = 0; j < n; j++) {
            weights[j] -= lr * gradient_w[j] / m;
        }
        bias -= lr * gradient_b / m;

        // Compute loss (optional)
        if (epoch % 100 == 0) {
            double loss = 0.0;
            for (int i = 0; i < m; i++) {
                double pred = predict(X[i], weights, bias);
                loss += -y[i] * log(pred) - (1 - y[i]) * log(1 - pred);
            }
            cout << "Epoch " << epoch << " - Loss: " << loss / m << endl;
        }
    }
}

// Predict class labels
vector<int> predictClasses(vector<vector<double>> X, vector<double> weights, double bias) {
    vector<int> predictions;
    for (auto& sample : X) {
        double prob = predict(sample, weights, bias);
        predictions.push_back(prob >= 0.5 ? 1 : 0);
    }
    return predictions;
}

// Load dataset from CSV
void loadCSV(const string& filename, vector<vector<double>>& X, vector<int>& y) {
    ifstream file(filename);
    string line;

    if (!file.is_open()) {
        cerr << "Error opening file: " << filename << endl;
        exit(1);
    }

    // Read data line by line
    while (getline(file, line)) {
        stringstream ss(line);
        vector<double> features;
        string value;
        int label;

        // Read features
        while (getline(ss, value, ',')) {
            if (ss.peek() == '\n' || ss.peek() == EOF) {
                label = stoi(value);  // Last column is the label
                break;
            }
            features.push_back(stod(value));
        }

        X.push_back(features);
        y.push_back(label);
    }

    file.close();
}

// Compute accuracy
double computeAccuracy(vector<int> y_true, vector<int> y_pred) {
    int correct = 0;
    for (size_t i = 0; i < y_true.size(); i++) {
        if (y_true[i] == y_pred[i]) correct++;
    }
    return (double)correct / y_true.size();
}

vector<double> logisticRegression(vector<vector<double>> positive,vector<vector<double>> negative){

    vector<vector<double>> X;
    
    vector<int> y;
    for(int i=0;i<positive.size();i++)y.push_back(1);
    for(int i=0;i<negative.size();i++)y.push_back(0);
    
    // Split into train and test sets (80% train, 20% test)
    
    X.reserve(positive.size() + negative.size()); // Optional: To optimize memory allocation
    X.insert(X.end(), positive.begin(), positive.end());  // Append pos
    X.insert(X.end(), negative.begin(), negative.end());  // Append neg

    vector<double> weights;
    double bias;
    double learning_rate = 0.01;
    int epochs = 1000;

    // Set weights for positive and negative classes
    double weight_positive = 10.0; // Higher weight for minority class (e.g., positive)
    double weight_negative = 1.0;  // Lower weight for majority class (e.g., negative)

    // Train the model with weight adjustment
    trainLogisticRegression(X, y, weights, bias, learning_rate, epochs, weight_positive, weight_negative);

    // Print the coefficients (weights) and bias
    cout << "Model Coefficients (Weights):" << endl;
    for (size_t i = 0; i < weights.size(); i++) {
        cout << "w" << i << ": " << weights[i] << endl;
    }
    cout << "Bias: " << bias << endl;

    // Make predictions
    //vector<int> predictions = predictClasses(X_test, weights, bias);

    weights.push_back(bias);
    return weights;
}


PREDICATE(analysis_1d,3){
  vector<int> pos,neg;

    term_t list = A1.unwrap();  // A1 is the input Prolog list
    term_t head = PL_new_term_ref();  // Temporary variable to hold elements
    term_t tail = PL_copy_term_ref(list);  // Copy of the list reference

    // Iterate through the Prolog list
    while (PL_get_list(tail, head, tail)) {
        double value;
        if (PL_get_float(head, &value)) {
            pos.push_back(value);
        } else {
            cerr << "Error: Non-number value in positive list!" << endl;
            return false;  // Fail if we encounter a non-integer
        }
    }


    term_t list2 = A2.unwrap();  // A1 is the input Prolog list
        term_t head2 = PL_new_term_ref();  // Temporary variable to hold elements
        term_t tail2 = PL_copy_term_ref(list2);  // Copy of the list reference

        // Iterate through the Prolog list
        while (PL_get_list(tail2, head2, tail2)) {
            double value;
            if (PL_get_float(head2, &value)) {
                neg.push_back(value);
            } else {
                cerr << "Error: Non-number value in negative list!" << endl;
                return false;  // Fail if we encounter a non-integer
            }
        }


    // Example: Unify A2 with the first element of the extracted list
    if (!pos.empty()) {
        return A3.unify_integer(pos.size());
    }

    return false;  // Fail if the list is empty
}


PREDICATE(analysis, 3) {
    vector<vector<double>> pos, neg;  // Store 2D lists

    term_t list = A1.unwrap();  // Extract first argument
    term_t head = PL_new_term_ref();
    term_t tail = PL_copy_term_ref(list);

    // Extract 2D positive list
    while (PL_get_list(tail, head, tail)) {
        if (PL_is_list(head)) {
            vector<double> inner_list;
            term_t inner_head = PL_new_term_ref();
            term_t inner_tail = PL_copy_term_ref(head);

            while (PL_get_list(inner_tail, inner_head, inner_tail)) {
                double value;
                if (PL_get_float(inner_head, &value)) {
                    inner_list.push_back(value);
                } else {
                    cerr << "Error: Non-number value in positive list!" << endl;
                    return false;
                }
            }

            if (!PL_get_nil(inner_tail)) {
                cerr << "Error: Improper positive list!" << endl;
                return false;
            }

            pos.push_back(inner_list);
        } else {
            cerr << "Error: Expected a list inside positive list!" << endl;
            return false;
        }
    }

    if (!PL_get_nil(tail)) {
        cerr << "Error: Improper outer positive list!" << endl;
        return false;
    }

    // Extract 2D negative list
    term_t list2 = A2.unwrap();
    term_t head2 = PL_new_term_ref();
    term_t tail2 = PL_copy_term_ref(list2);

    while (PL_get_list(tail2, head2, tail2)) {
        if (PL_is_list(head2)) {
            vector<double> inner_list;
            term_t inner_head = PL_new_term_ref();
            term_t inner_tail = PL_copy_term_ref(head2);

            while (PL_get_list(inner_tail, inner_head, inner_tail)) {
                double value;
                if (PL_get_float(inner_head, &value)) {
                    inner_list.push_back(value);
                } else {
                    cerr << "Error: Non-number value in negative list!" << endl;
                    return false;
                }
            }

            if (!PL_get_nil(inner_tail)) {
                cerr << "Error: Improper negative list!" << endl;
                return false;
            }

            neg.push_back(inner_list);
        } else {
            cerr << "Error: Expected a list inside negative list!" << endl;
            return false;
        }
    }

    if (!PL_get_nil(tail2)) {
        cerr << "Error: Improper outer negative list!" << endl;
        return false;
    }

    vector<double> vec = logisticRegression(pos,neg);
    // Example: Unify A3 with the total number of inner lists in A1
    term_t prolog_list = PL_new_term_ref();
    PL_put_nil(prolog_list);  // Start with an empty list

    // Build the list from the vector
    for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
        term_t head = PL_new_term_ref();
        PL_put_float(head, *it);  
        PL_cons_list(prolog_list, head, prolog_list);  
    }
    PlTerm pl_list(prolog_list);
    // Unify A3 with the constructed Prolog list
    return A3.unify_term(pl_list);
}