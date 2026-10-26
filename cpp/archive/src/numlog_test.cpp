#include <iostream>
#include <vector>
#include <fstream>
#include <sstream>
#include <cmath>
#include <cstdlib>
#include <ctime>

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

int main(int argc, char** argv) {
    vector<vector<double>> X;
    vector<int> y;

    // Load the Breast Cancer dataset (CSV file with 30 features + label)
    loadCSV("../../breast_cancer.csv", X, y);

    // Split into train and test sets (80% train, 20% test)
    int train_size = X.size() * 0.8;
    vector<vector<double>> X_train(X.begin(), X.begin() + train_size);
    vector<vector<double>> X_test(X.begin() + train_size, X.end());
    vector<int> y_train(y.begin(), y.begin() + train_size);
    vector<int> y_test(y.begin() + train_size, y.end());

    vector<double> weights;
    double bias;
    double learning_rate = 0.01;
    int epochs = 1000;

    // Set weights for positive and negative classes
    double weight_positive = 10.0; // Higher weight for minority class (e.g., positive)
    double weight_negative = 1.0;  // Lower weight for majority class (e.g., negative)

    // Train the model with weight adjustment
    trainLogisticRegression(X_train, y_train, weights, bias, learning_rate, epochs, weight_positive, weight_negative);

    // Print the coefficients (weights) and bias
    cout << "Model Coefficients (Weights):" << endl;
    for (size_t i = 0; i < weights.size(); i++) {
        cout << "w" << i << ": " << weights[i] << endl;
    }
    cout << "Bias: " << bias << endl;

    // Make predictions
    vector<int> predictions = predictClasses(X_test, weights, bias);

    // Compute accuracy
    double accuracy = computeAccuracy(y_test, predictions);
    cout << "Test Accuracy: " << accuracy * 100 << "%" << endl;

    string head[] = {"mean_radius","mean_texture","mean_perimeter","mean_area","mean_smoothness","mean_compactness","mean_concavity","mean_concave_points","mean_symmetry","mean_fractal_dimension","radius_error","texture_error","perimeter_error","area_error","smoothness_error","compactness_error","concavity_error","concave_points_error","symmetry_error","fractal_dimension_error","worst_radius","worst_texture","worst_perimeter","worst_area","worst_smoothness","worst_compactness","worst_concavity","worst_concave_points","worst_symmetry","worst_fractal_dimension","target"};
    cout<<"Hypothesis:"<<endl;
    vector<int> addrs;
    cout<<"rule(A):-"<<endl;
    for (size_t i = 0; i < weights.size(); i++) {
        if(weights[i]>1){
            srand(time(0)); // Seed the random number generator with the current time
             int randomNumber = 1000 + std::rand() % 9000;
             addrs.push_back(randomNumber);
            cout <<"\t"<<head[i]<< "(A, _" <<randomNumber<<"),"<<endl;
        }

    }

    cout<<"_rule(";
    for(int i=0;i<addrs.size();i++){
        cout<<addrs.at(i)<<", ";
    }
    cout<<")."<<endl;

    cout<<"_rule(";
    int j=0;
    for (size_t i = 0; i < weights.size(); i++) {
        if(weights[i]>1){
             cout<<"_"<<addrs.at(j)<<", ";
             j++;
        }
    }
    cout<<"):-"<<endl<<"\t";
    j=0;
    for (size_t i = 0; i < weights.size(); i++) {
        if(weights[i]>1){
             cout<<"_"<<addrs.at(j)<<"*"<<weights[i]<<" - ";
             j++;
        }

    }
    cout<<bias<<".";

    return 0;
}
