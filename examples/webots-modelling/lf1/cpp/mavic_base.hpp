#pragma once

#include <webots/GPS.hpp>
#include <webots/Gyro.hpp>
#include <webots/InertialUnit.hpp>
#include <webots/Motor.hpp>
#include <webots/Robot.hpp>

#include <algorithm>
#include <array>

class MavicBase : public webots::Robot {
public:
  MavicBase();
  void run();

protected:
  struct Pose {
    double x{}, y{}, z{};
    double roll{}, pitch{}, yaw{};
  };

  // Subclasses fill in disturbances + altitude target each tick.
  // Defaults already zeroed; subclasses only set what they care about.
  struct Controls {
    double yaw{};
    double pitch{};
    double roll{};
    double target_altitude{};
  };

  virtual Controls computeControls(const Pose& pose) = 0;

  static constexpr double K_VERTICAL_THRUST = 68.5;
  static constexpr double K_VERTICAL_OFFSET = 0.6;
  static constexpr double K_VERTICAL_P = 3.0;
  static constexpr double K_ROLL_P = 50.0;
  static constexpr double K_PITCH_P = 30.0;
  static constexpr double MAX_YAW_DISTURBANCE = 0.4;
  static constexpr double MAX_PITCH_DISTURBANCE = -1.0;

  static constexpr double clamp(double v, double lo, double hi) {
    return std::min(std::max(v, lo), hi);
  }

  int timeStep() const { return time_step_; }

private:
  int time_step_;
  webots::InertialUnit* imu_;
  webots::GPS* gps_;
  webots::Gyro* gyro_;
  std::array<webots::Motor*, 4> motors_;
};
