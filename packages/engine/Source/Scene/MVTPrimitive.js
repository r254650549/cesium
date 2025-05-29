import BoundingSphere from "../Core/BoundingSphere.js";
import Cartesian3 from "../Core/Cartesian3.js";
import Color from "../Core/Color.js";
import ColorGeometryInstanceAttribute from "../Core/ColorGeometryInstanceAttribute.js";
import combine from "../Core/combine.js";
import ComponentDatatype from "../Core/ComponentDatatype.js";
import createGuid from "../Core/createGuid.js";
import defined from "../Core/defined.js";
import destroyObject from "../Core/destroyObject.js";
import DeveloperError from "../Core/DeveloperError.js";
import Event from "../Core/Event.js";
import GeometryAttribute from "../Core/GeometryAttribute.js";
import GeometryInstance from "../Core/GeometryInstance.js";
import PrimitiveType from "../Core/PrimitiveType.js";
import Rectangle from "../Core/Rectangle.js";
import Resource from "../Core/Resource.js";
import RuntimeError from "../Core/RuntimeError.js";
import WebMercatorTilingScheme from "../Core/WebMercatorTilingScheme.js";
import GeographicTilingScheme from "../Core/GeographicTilingScheme.js";
import PerInstanceColorAppearance from "./PerInstanceColorAppearance.js";
import Primitive from "./Primitive.js";
// 贴地几何体相关导入
import Appearance from "./Appearance.js"; // Added import
import GroundPrimitive from "./GroundPrimitive.js";
import ClassificationType from "./ClassificationType.js";
import PolygonGeometry from "../Core/PolygonGeometry.js";
import PolygonOutlineGeometry from "../Core/PolygonOutlineGeometry.js"; // Ensure this import is present
import PolygonHierarchy from "../Core/PolygonHierarchy.js";
import GroundPolylinePrimitive from "./GroundPolylinePrimitive.js";
import GroundPolylineGeometry from "../Core/GroundPolylineGeometry.js";
import Material from "./Material.js"; // Added import
import MaterialAppearance from "./MaterialAppearance.js"; // Added import
import PointPrimitiveCollection from "./PointPrimitiveCollection.js"; // Added import
import VerticalOrigin from "./VerticalOrigin.js"; // Added for billboard positioning
import HeightReference from "./HeightReference.js"; // Added import
import BillboardCollection from "./BillboardCollection.js"; // Added for billboard style points

// 导入MVT解析所需的库
import { VectorTile } from "@mapbox/vector-tile";
import Pbf from "pbf";

// 默认样式属性
const defaultStroke = Color.BLACK; // Changed from YELLOW to BLACK for better contrast
const defaultStrokeWidth = 2.5; // Increased from 2 to 2.5 for better visibility
const defaultFill = Color.fromBytes(255, 255, 0, 100);
const defaultMarkerColor = Color.ROYALBLUE;
const defaultMarkerSize = 48;
const defaultClampToGround = true; // 默认开启贴地
const defaultPointStyle = "billboard"; // 'billboard', 'point', or 'label'
const defaultPointSize = 10;
const defaultPointColor = Color.ROYALBLUE;
const defaultOutline = true; // 默认显示轮廓线
const defaultOutlineColor = Color.BLACK; // 默认轮廓线颜色
const defaultOutlineWidth = 2.0; // 默认轮廓线宽度
// 默认地图点位图标
const DEFAULT_MAP_POINT_IMAGE = "../../../Source/Assets/Images/map_point.png";

// 支持的投影类型
const ProjectionType = {
  WEBMERCATOR: "webmercator", // EPSG:900913/3857
  GEOGRAPHIC: "geographic", // EPSG:4326
};

// MVT默认范围
const DEFAULT_EXTENT = 4096;

// 用于批处理的常量
const MAXIMUM_BATCH_SIZE = 8000; // 最多一次批处理多少个实例

// 面渲染的高度偏移量，避免z-fighting
const POLYGON_HEIGHT_OFFSET = 10.0;

/**
 * A primitive that renders Mapbox Vector Tile format data (MVT) using lower-level rendering for optimal performance.
 * It's designed to handle large-scale vector tiles more efficiently than the {@link MVTDataSource}.
 *
 * @alias MVTPrimitive
 * @constructor
 *
 * @param {Object} [options] Object with the following properties:
 * @param {String} [options.name] The name of this primitive.
 * @param {Boolean} [options.show=true] Determines if this primitive will be shown.
 * @param {MVTPrimitive.StyleOptions} [options.style] Style options applied to all features.
 * @param {Boolean} [options.clampToGround=false] Whether to clamp geometries to terrain.
 * @param {String} [options.projection='geographic'] Projection type: 'webmercator' (EPSG:3857) or 'geographic' (EPSG:4326).
 * @param {HTMLCanvasElement|String|Image} [options.billboardImage] A custom image to use for points when pointStyle is 'billboard'.
 * @param {Viewer|Scene} [options.viewer] The Cesium Viewer or Scene instance. Required for billboard creation with height reference.
 */
function MVTPrimitive(options) {
  options = options || {};

  /**
   * @type {String}
   */
  this._name = options.name;

  /**
   * @type {Boolean}
   */
  this._show = options.show !== undefined ? options.show : true;

  /**
   * @type {MVTPrimitive.StyleOptions}
   * @private
   */
  this._style = options.style || {};

  /**
   * @type {Boolean}
   * @private
   */
  this._clampToGround =
    options.clampToGround !== undefined
      ? options.clampToGround
      : defaultClampToGround;

  /**
   * @type {String}
   * @private
   */
  this._projectionType = options.projection || ProjectionType.WEBMERCATOR;

  /**
   * @type {Viewer|Scene}
   * @private
   */
  this._viewer = options.viewer;

  /**
   * @type {Array.<Primitive|GroundPrimitive|GroundPolylinePrimitive|PointPrimitiveCollection>}
   * @private
   */
  this._primitives = [];
  /**
   * @type {PointPrimitiveCollection}
   * @private
   */
  this._pointPrimitiveCollection = null; // Added for clamped points
  /**
   * @type {BillboardCollection}
   * @private
   */
  this._billboardCollection = null; // Added for billboard style points

  /**
   * @type {HTMLCanvasElement|String|Image}
   * @private
   */
  this._billboardImage = options.billboardImage; // Custom image for billboards

  /**
   * @type {Array.<Object>}
   * @private
   */
  this._geometryInstances = [];

  /**
   * @type {Object.<String, Array.<Object>>}
   * @private
   */
  this._geometryBatches = {
    polygons: [],
    regularPolylines: [], // For raw line geometry (rendered with Primitive)
    groundPolylines: [], // For GroundPolylineGeometry (rendered with GroundPolylinePrimitive)
    points: [],
    polygonOutlines: [], // For non-ground PolygonOutlineGeometry (rendered with Primitive)
  };

  /**
   * @type {String}
   * @private
   */
  this._urlTemplate = undefined;

  /**
   * @type {Object}
   * @private
   */
  this._options = {};
  /**
   * @type {TilingScheme}
   * @private
   */
  this._tilingScheme =
    this._projectionType === ProjectionType.GEOGRAPHIC
      ? new GeographicTilingScheme()
      : new WebMercatorTilingScheme();

  /**
   * @type {Function}
   * @private
   */
  this._layerFilter = undefined;

  /**
   * @type {Event}
   */
  this.readyPromise = new Event();

  /**
   * @type {Event}
   */
  this._changed = new Event();

  /**
   * @type {Event}
   */
  this._error = new Event();

  /**
   * @type {Event}
   */
  this._loading = new Event();

  /**
   * @type {Boolean}
   * @private
   */
  this._isLoading = false;

  /**
   * @type {Boolean}
   * @private
   */
  this._ready = false;

  /**
   * @type {Number}
   * @private
   */
  this._zoom = 0;

  /**
   * @type {Promise}
   * @private
   */
  this._tilesLoadingPromise = undefined;
}

Object.defineProperties(MVTPrimitive.prototype, {
  /**
   * The name of this primitive.
   * @memberof MVTPrimitive.prototype
   * @type {String}
   */
  name: {
    get: function () {
      return this._name;
    },
    set: function (value) {
      if (this._name !== value) {
        this._name = value;
        this._changed.raiseEvent(this);
      }
    },
  },

  /**
   * Determines if this primitive will be shown.
   * @memberof MVTPrimitive.prototype
   * @type {Boolean}
   */ show: {
    get: function () {
      return this._show;
    },
    set: function (value) {
      this._show = value;
      for (let i = 0; i < this._primitives.length; i++) {
        this._primitives[i].show = value;
      }
    },
  },

  /**
   * Gets the event that is raised when the primitive has loaded.
   * @memberof MVTPrimitive.prototype
   * @type {Event}
   * @readonly
   */
  readyEvent: {
    get: function () {
      return this.readyPromise;
    },
  },

  /**
   * Gets the event that is raised when the primitive changes.
   * @memberof MVTPrimitive.prototype
   * @type {Event}
   * @readonly
   */
  changedEvent: {
    get: function () {
      return this._changed;
    },
  },

  /**
   * Gets the event that is raised when the primitive encounters an error.
   * @memberof MVTPrimitive.prototype
   * @type {Event}
   * @readonly
   */
  errorEvent: {
    get: function () {
      return this._error;
    },
  },

  /**
   * Gets the event that is raised when the primitive is loading data.
   * @memberof MVTPrimitive.prototype
   * @type {Event}
   * @readonly
   */
  loadingEvent: {
    get: function () {
      return this._loading;
    },
  },

  /**
   * Gets whether the primitive is in the process of loading data.
   * @memberof MVTPrimitive.prototype
   * @type {Boolean}
   * @readonly
   */
  isLoading: {
    get: function () {
      return this._isLoading;
    },
  },

  /**
   * Gets whether the primitive's data is loaded and ready for rendering.
   * @memberof MVTPrimitive.prototype
   * @type {Boolean}
   * @readonly
   */
  ready: {
    get: function () {
      return this._ready;
    },
  },
});

/**
 * Asynchronously loads MVT data from a URL. The URL can be a template with {x}, {y}, {z} parameters
 * for loading MVT tiles based on a tiling scheme.
 *
 * @param {String|Resource} url The URL to load MVT data from.
 * @param {Object} [options] Options object with properties:
 * @param {Object} [options.style] Style properties to apply to the MVT data.
 * @param {Number} [options.x] Optional X coordinate for tile request.
 * @param {Number} [options.y] Optional Y coordinate for tile request.
 * @param {Number} [options.zoom] Optional zoom level for tile request.
 * @param {Boolean} [options.clampToGround] Whether to clamp features to the ground.
 * @returns {Promise<MVTPrimitive>} A promise that resolves when the data is loaded.
 */
MVTPrimitive.prototype.load = function (url, options) {
  options = options || {};
  this._options = options;
  this._style = options.style || this._style;
  this._clampToGround =
    options.clampToGround !== undefined
      ? options.clampToGround
      : this._clampToGround;

  if (typeof url === "string") {
    // Check if URL is a template with {x}, {y}, {z} parameters
    if (
      url.indexOf("{x}") !== -1 &&
      url.indexOf("{y}") !== -1 &&
      url.indexOf("{z}") !== -1
    ) {
      this._urlTemplate = url;

      console.log(`URL detected as XYZ format: ${url}`);

      // If specific x, y, zoom were provided, load a specific tile
      if (defined(options.x) && defined(options.y) && defined(options.zoom)) {
        const finalUrl = url
          .replace("{x}", options.x)
          .replace("{y}", options.y)
          .replace("{z}", options.zoom);

        this._zoom = options.zoom;
        return this._loadTile(finalUrl, options);
      }

      // Otherwise load default center tile at lowest zoom level
      const initialZoom = options.zoom || 1;
      const initialX = options.x || Math.pow(2, initialZoom - 1);
      const initialY = options.y || Math.pow(2, initialZoom - 1);

      const initialUrl = url
        .replace("{x}", initialX)
        .replace("{y}", initialY)
        .replace("{z}", initialZoom);

      this._zoom = initialZoom;
      console.log(
        `Loading initial tile: zoom=${initialZoom}, x=${initialX}, y=${initialY}`,
      );
      return this._loadTile(initialUrl, {
        ...options,
        x: initialX,
        y: initialY,
        zoom: initialZoom,
      });
    }
  }

  // If it's not a template URL, load the provided URL directly
  return this._loadTile(url, options);
};

/**
 * Adds a tile to the primitive without removing existing tiles.
 * @param {String|Resource} url The URL to load MVT data from.
 * @param {Object} [options] Options for loading the tile.
 * @returns {Promise<MVTPrimitive>} A promise that resolves when the tile has loaded.
 */
MVTPrimitive.prototype.process = function (url, options) {
  return this._loadTile(url, options, false);
};

/**
 * Loads multiple tiles within the given rectangle and zoom level.
 * @param {Object} options Object with properties:
 * @param {Rectangle} options.rectangle The visible rectangle to load tiles for.
 * @param {Number} options.zoom The zoom level to load.
 * @param {Boolean} [options.clear=true] Whether to clear existing tiles.
 * @returns {Promise<MVTPrimitive>} A promise that resolves when all tiles have loaded.
 */
MVTPrimitive.prototype.updateViewport = function (options) {
  if (!defined(options.rectangle) || !defined(options.zoom)) {
    throw new DeveloperError("rectangle and zoom are required.");
  }

  if (!defined(this._urlTemplate)) {
    throw new DeveloperError(
      "URL template must be set before updating viewport.",
    );
  }

  if (this._tilesLoadingPromise) {
    return this._tilesLoadingPromise;
  }

  const zoom = Math.floor(options.zoom);

  // Use appropriate tiling scheme based on projection
  const tilingScheme = this._tilingScheme;

  // Calculate tile range
  let west = 0;
  let east = Math.pow(2, zoom) - 1;
  let north = 0;
  let south = Math.pow(2, zoom) - 1;

  try {
    // Get the northwest and southeast corners of the view rectangle
    const nwTile = tilingScheme.positionToTileXY(
      Rectangle.northwest(options.rectangle),
      zoom,
    );
    const seTile = tilingScheme.positionToTileXY(
      Rectangle.southeast(options.rectangle),
      zoom,
    );

    if (defined(nwTile) && defined(seTile)) {
      if (this._projectionType === ProjectionType.GEOGRAPHIC) {
        // For geographic projection (EPSG:4326), the GeographicTilingScheme.positionToTileXY
        // already handles coordinate calculation correctly:
        // - North latitudes get smaller Y values
        // - Just need bounds checking, not coordinate flipping
        west = Math.max(0, Math.min(nwTile.x, seTile.x));
        east = Math.min(
          tilingScheme.getNumberOfXTilesAtLevel(zoom) - 1,
          Math.max(nwTile.x, seTile.x),
        );
        north = Math.max(0, Math.min(nwTile.y, seTile.y));
        south = Math.min(
          tilingScheme.getNumberOfYTilesAtLevel(zoom) - 1,
          Math.max(nwTile.y, seTile.y),
        );

        console.log(
          `Geographic projection viewport: zoom=${zoom}, tiles=(${west}-${east}, ${north}-${south})`,
        );
      } else {
        // WebMercator handles differently
        west = Math.max(0, nwTile.x);
        east = Math.min(Math.pow(2, zoom) - 1, seTile.x);
        north = Math.max(0, nwTile.y);
        south = Math.min(Math.pow(2, zoom) - 1, seTile.y);

        console.log(
          `WebMercator projection viewport: zoom=${zoom}, tiles=(${west}-${east}, ${north}-${south})`,
        );
      }

      // Validate tile ranges
      if (east < west || south < north) {
        console.warn(
          `Invalid tile range calculated: (${west}-${east}, ${north}-${south}). Swapping coordinates.`,
        );
        if (east < west) {
          const temp = east;
          east = west;
          west = temp;
        }
        if (south < north) {
          const temp = south;
          south = north;
          north = temp;
        }
      }
    } else {
      console.warn(
        "Failed to calculate tile coordinates from rectangle. Using default tile range.",
      );
    }
  } catch (e) {
    console.error("Error calculating tile bounds:", e);
  }

  // Clear existing primitives if needed
  if (options.clear !== false) {
    this._clearExistingPrimitives();
  }

  // Load visible tiles
  const promises = [];
  const baseOptions = { ...this._options };
  const maxTiles = 100; // Limit to prevent overloading
  let tileCount = 0;
  let tilesRequested = false;

  console.log(
    `Starting tile loading: x=${west}-${east}, y=${north}-${south}, zoom=${zoom}`,
  );

  // Ensure west <= east and north <= south for the loop
  const westBound = Math.min(west, east);
  const eastBound = Math.max(west, east);
  const northBound = Math.min(north, south);
  const southBound = Math.max(north, south);
  for (let x = westBound; x <= eastBound && tileCount < maxTiles; x++) {
    for (let y = northBound; y <= southBound && tileCount < maxTiles; y++) {
      const tileOptions = {
        ...baseOptions,
        x: x,
        y: y,
        zoom: zoom,
      };

      const url = this._urlTemplate
        .replace("{x}", x)
        .replace("{y}", y)
        .replace("{z}", zoom + 1);

      console.log(`Requesting tile: ${url}`);

      promises.push(this.process(url, tileOptions));
      tileCount++;
      tilesRequested = true;
    }
  }

  // If no tiles were requested, try requesting a default central tile
  if (!tilesRequested) {
    console.warn(
      "No tiles in calculated range. Requesting default central tile.",
    );
    const x = Math.floor(Math.pow(2, zoom - 1));
    const y = Math.floor(Math.pow(2, zoom - 1));

    const url = this._urlTemplate
      .replace("{x}", x)
      .replace("{y}", y)
      .replace("{z}", zoom);

    console.log(`Requesting default central tile: ${url}`);
    promises.push(
      this.process(url, { ...baseOptions, x: x, y: y, zoom: zoom }),
    );
  }

  this._zoom = zoom;
  this._tilesLoadingPromise = Promise.all(promises)
    .then(() => {
      console.log(`All ${promises.length} tiles loaded successfully`);
      this._finalizePrimitive();
      this._tilesLoadingPromise = undefined;
      return this;
    })
    .catch((error) => {
      console.error("Error loading tiles:", error);
      this._tilesLoadingPromise = undefined;
      this._error.raiseEvent(this, error);
      return Promise.reject(error);
    });

  return this._tilesLoadingPromise;
};

/**
 * Updates the primitive's appearance properties.
 * @param {MVTPrimitive.StyleOptions} style The new style options.
 */
MVTPrimitive.prototype.updateStyle = function (style) {
  this._style = combine(this._style, style);
  // Apply style changes to existing primitives
  this._recreatePrimitives();
};

/**
 * Sets the URL template for loading tiles
 * @param {string} template URL template with {x}, {y}, {z} placeholders
 * @returns {MVTPrimitive} This instance for chaining
 */
MVTPrimitive.prototype.setUrlTemplate = function (template) {
  this._urlTemplate = template;
  return this;
};

/**
 * Sets a filter function to selectively load layers from MVT tiles.
 * @param {Function} filter A function that takes a layer name and returns true to include it or false to exclude it
 * @returns {MVTPrimitive} This instance for chaining
 */
MVTPrimitive.prototype.setLayerFilter = function (filter) {
  this._layerFilter = filter;
  return this;
};

/**
 * Loads a single MVT tile from the given URL.
 * @private
 * @param {String|Resource} url The URL to load MVT data from.
 * @param {Object} options Options for loading the tile.
 * @param {Boolean} [clear=true] Whether to clear existing data before loading.
 * @returns {Promise<MVTPrimitive>} A promise that resolves when the tile has loaded.
 */
MVTPrimitive.prototype._loadTile = function (url, options, clear = true) {
  options = options || {};

  // Track loading state
  this._isLoading = true;
  this._loading.raiseEvent(this);

  if (clear) {
    this._clearExistingPrimitives();
  }

  // Build resource from URL
  let resource;
  if (typeof url === "string" || url instanceof Resource) {
    resource = Resource.createIfNeeded(url);
  } else {
    return Promise.reject(
      new DeveloperError("url is required and must be a string or Resource."),
    );
  }

  // Get style options
  const styleOptions = this._prepareStyleOptions(options);

  // Fetch tile data
  return resource
    .fetchArrayBuffer()
    .then((mvtBuffer) => {
      return this._processMvtTile(mvtBuffer, styleOptions, options);
    })
    .catch((error) => {
      this._isLoading = false;
      this._error.raiseEvent(this, error);
      return Promise.reject(error);
    });
};

/**
 * Prepares style options by combining passed options with defaults.
 * @private
 * @param {Object} options Source options.
 * @returns {Object} Merged style options.
 */
MVTPrimitive.prototype._prepareStyleOptions = function (options) {
  options = options || {};

  // Merge style options with defaults
  return {
    stroke: options.stroke || this._style.stroke || defaultStroke,
    strokeWidth:
      options.strokeWidth || this._style.strokeWidth || defaultStrokeWidth,
    fill: options.fill || this._style.fill || defaultFill,
    markerColor:
      options.markerColor || this._style.markerColor || defaultMarkerColor,
    markerSize:
      options.markerSize || this._style.markerSize || defaultMarkerSize,
    clampToGround: this._clampToGround, // Uses the primitive's clampToGround setting
    pointStyle:
      options.pointStyle || this._style.pointStyle || defaultPointStyle,
    pointColor:
      options.pointColor || this._style.pointColor || defaultPointColor,
    pointSize: options.pointSize || this._style.pointSize || defaultPointSize,
    outline:
      options.outline !== undefined
        ? options.outline
        : this._style.outline !== undefined
          ? this._style.outline
          : defaultOutline,
    outlineColor:
      options.outlineColor || this._style.outlineColor || defaultOutlineColor,
    outlineWidth:
      options.outlineWidth || this._style.outlineWidth || defaultOutlineWidth,
    x: options.x,
    y: options.y,
    zoom: options.zoom || this._zoom,
  };
};

/**
 * Process MVT tile data and create geometry instances.
 * @private
 * @param {ArrayBuffer} mvtBuffer The MVT binary data.
 * @param {Object} styleOptions Style options to apply.
 * @param {Object} options General loading options.
 * @returns {Promise<MVTPrimitive>} A promise that resolves when processing is complete.
 */
MVTPrimitive.prototype._processMvtTile = function (
  mvtBuffer,
  styleOptions,
  options,
) {
  try {
    // Parse MVT data
    const vectorTile = this._decodeMVT(mvtBuffer);

    // Process each layer
    for (const layerName in vectorTile.layers) {
      if (!vectorTile.layers.hasOwnProperty(layerName)) {
        continue;
      }

      // Apply layer filter if one exists
      if (defined(this._layerFilter) && !this._layerFilter(layerName)) {
        continue;
      }

      const layer = vectorTile.layers[layerName];
      console.log("MVTPrimitive: Processing layer", layerName, layer);
      this._processLayer(layer, styleOptions);
    }

    // Create primitives if we're not in the middle of loading multiple tiles
    if (!this._tilesLoadingPromise) {
      this._finalizePrimitive();
    }

    this._isLoading = false;
    this._ready = true;
    this.readyPromise.raiseEvent(this);

    return this;
  } catch (error) {
    this._isLoading = false;
    this._error.raiseEvent(this, error);
    return Promise.reject(error);
  }
};

/**
 * Clears any existing primitives.
 * @private
 */
MVTPrimitive.prototype._clearExistingPrimitives = function () {
  // Destroy primitives
  for (let i = 0; i < this._primitives.length; i++) {
    // Check if destroy function exists, as PointPrimitiveCollection might be in the list
    if (typeof this._primitives[i].destroy === "function") {
      this._primitives[i].destroy();
    } else if (defined(this._primitives[i].removeAll)) {
      // For PointPrimitiveCollection
      this._primitives[i].removeAll();
    }
  }
  this._primitives = [];

  // Explicitly handle _pointPrimitiveCollection if it was created and added to _primitives
  // The loop above should handle its destruction if it was added to _primitives.
  // If it was managed completely separately:
  // if (defined(this._pointPrimitiveCollection) && !this._pointPrimitiveCollection.isDestroyed()) {
  //     this._pointPrimitiveCollection.destroy();
  // }
  // Clean up point primitive collection
  this._pointPrimitiveCollection = null; // Reset

  // Clean up billboard collection
  this._billboardCollection = null;

  // Clear arrays
  // this._geometryInstances = []; // This line was commented out, ensure it's intended. If used by _recreatePrimitives, it needs careful handling.
  this._geometryBatches = {
    polygons: [],
    regularPolylines: [],
    groundPolylines: [],
    points: [], // Will now only store non-clamped points
    polygonOutlines: [],
  };
};

/**
 * Recreates primitives after style changes.
 * @private
 */
MVTPrimitive.prototype._recreatePrimitives = function () {
  // Store current instances (primarily for non-point geometries or non-clamped points)
  const oldInstances = this._geometryInstances.slice();

  // Instead of clearing everything, selectively update primitives
  if (this._pointPrimitiveCollection) {
    this._pointPrimitiveCollection.removeAll(); // Clear existing points but keep the collection
  }

  // For features that were originally processed into _geometryInstances (e.g., non-clamped points, lines, polygons before ground conversion)
  // This part of the logic might need review if _geometryInstances is the sole source for recreating all feature types.
  // If MVT data needs to be re-processed entirely for style changes (especially for PointPrimitiveCollection items),
  // this simple instance restoration might not be enough.
  this._geometryInstances = oldInstances;

  // Re-create primitives with new style
  // This will re-process features if _loadTile or _processMvtTile is called again.
  // For now, _finalizePrimitive will try to build from existing _geometryBatches or _geometryInstances.
  // This might not correctly update points in a PointPrimitiveCollection that were added with old style values.
  // A more robust updateStyle would re-process the source MVT data for the current tiles.
  this._finalizePrimitive();
};

/**
 * Finalizes primitive creation after all tile processing.
 * @private
 */
MVTPrimitive.prototype._finalizePrimitive = function () {
  // Batch geometry by type for better performance
  console.time("Batch and Create Primitives"); // Add timing to measure performance
  this._batchAndCreatePrimitives();
  console.timeEnd("Batch and Create Primitives");

  // Update ready state
  this._ready = true;
  this.readyPromise.raiseEvent(this);

  // Log a summary of created primitives
  console.log("MVTPrimitive: All primitives created.", {
    clampToGround: this._clampToGround,
    totalPrimitives: this._primitives.length,
    polygons: this._geometryBatches.polygons.length,
    regularPolylines: this._geometryBatches.regularPolylines.length,
    groundPolylines: this._geometryBatches.groundPolylines.length,
    points: this._geometryBatches.points.length,
    polygonOutlines: this._geometryBatches.polygonOutlines.length,
  });
};

/**
 * Batch geometries by type and create final primitives.
 * @private
 */
MVTPrimitive.prototype._batchAndCreatePrimitives = function () {
  console.time("Batch Geometry Processing"); // Add timing to measure performance

  // Create primitives for each batch
  if (this._geometryBatches.polygons.length > 0) {
    this._createPolygonPrimitives();
  }
  if (this._geometryBatches.regularPolylines.length > 0) {
    this._createRegularPolylinePrimitives();
  }
  if (this._geometryBatches.groundPolylines.length > 0) {
    this._createGroundPolylinePrimitives();
  }
  if (this._geometryBatches.points.length > 0) {
    this._createPointPrimitives();
  }
  if (this._geometryBatches.polygonOutlines.length > 0) {
    this._createPolygonOutlinePrimitives();
  }

  console.timeEnd("Batch Geometry Processing");

  // Clear batch arrays
  this._geometryBatches = {
    polygons: [],
    regularPolylines: [],
    groundPolylines: [],
    points: [],
    polygonOutlines: [],
  };
};

/**
 * Creates polygon primitives from batched geometries.
 * @private
 */
MVTPrimitive.prototype._createPolygonPrimitives = function () {
  const polygonBatches = this._geometryBatches.polygons;
  if (polygonBatches.length === 0) {
    return;
  }

  // Create primitives from batches (create multiple primitives if needed to stay under the instance limit)
  for (let i = 0; i < polygonBatches.length; i++) {
    const batch = polygonBatches[i];
    if (batch.length === 0) {
      continue;
    }

    const primitive = new GroundPrimitive({
      geometryInstances: batch,
      classificationType: ClassificationType.TERRAIN,
      asynchronous: false,
    });

    primitive.show = this._show;
    this._primitives.push(primitive);
  }
};

/**
 * Creates regular polyline primitives (using standard Primitive) from batched raw line geometries.
 * @private
 */
MVTPrimitive.prototype._createRegularPolylinePrimitives = function () {
  const polylineBatches = this._geometryBatches.regularPolylines;
  if (!polylineBatches || polylineBatches.length === 0) {
    return;
  }

  const styleStrokeColor = this._style.stroke || defaultStroke;
  const isTranslucent = styleStrokeColor.alpha < 1.0;

  // Determine a suitable render state
  const renderState = Appearance.getDefaultRenderState(
    isTranslucent,
    false,
    undefined,
  );
  // Customize if necessary, e.g., lineWidth, though it has limitations
  const maximumAliasedLineWidth = 1.0; // Default maximum for most WebGL implementations
  renderState.lineWidth = Math.min(
    this._style.strokeWidth || defaultStrokeWidth,
    maximumAliasedLineWidth,
  );
  if (isTranslucent) {
    renderState.depthMask = false; // Common for translucent blending
  }

  const appearance = new PerInstanceColorAppearance({
    flat: true,
    translucent: isTranslucent,
    renderState: renderState,
  });

  for (let i = 0; i < polylineBatches.length; i++) {
    const batch = polylineBatches[i];
    if (batch.length === 0) {
      continue;
    }

    const primitive = new Primitive({
      geometryInstances: batch,
      appearance: appearance,
      asynchronous: false,
    });

    primitive.show = this._show;
    this._primitives.push(primitive);
  }
};

/**
 * Creates ground polyline primitives from batched GroundPolylineGeometry.
 * @private
 */
MVTPrimitive.prototype._createGroundPolylinePrimitives = function () {
  const polylineBatches = this._geometryBatches.groundPolylines;
  if (!polylineBatches || polylineBatches.length === 0) {
    return;
  }

  const styleOutlineColor = this._style.outlineColor || defaultOutlineColor;
  const isTranslucent = styleOutlineColor.alpha < 1.0;

  // GroundPolylinePrimitive expects an appearance with a material.
  // Use MaterialAppearance with a single color for these.
  const renderState = Appearance.getDefaultRenderState(
    isTranslucent,
    false,
    undefined,
  );
  if (isTranslucent) {
    renderState.depthMask = false;
  }
  // lineWidth for MaterialAppearance on GroundPolylinePrimitive is not typically set via renderState,
  // as GroundPolylineGeometry itself has a 'width' property.

  const appearance = new MaterialAppearance({
    material: Material.fromType("Color", { color: styleOutlineColor }),
    flat: true,
    faceForward: false,
    translucent: isTranslucent, // MaterialAppearance also has a translucent property
    renderState: renderState,
  });

  for (let i = 0; i < polylineBatches.length; i++) {
    const batch = polylineBatches[i];
    if (batch.length === 0) {
      continue;
    }

    const primitive = new GroundPolylinePrimitive({
      geometryInstances: batch,
      appearance: appearance,
      asynchronous: false,
    });

    primitive.show = this._show;
    this._primitives.push(primitive);
  }
};

/**
 * Creates point primitives from batched geometries.
 * @private
 */
MVTPrimitive.prototype._createPointPrimitives = function () {
  const pointBatches = this._geometryBatches.points; // These are now only non-clamped points
  if (!pointBatches || pointBatches.length === 0) {
    return;
  }

  // Use a single PointPrimitiveCollection for all points in the batch
  if (!this._pointPrimitiveCollection) {
    this._pointPrimitiveCollection = new PointPrimitiveCollection();
    this._primitives.push(this._pointPrimitiveCollection);
  }

  const pointColor = this._style.pointColor || defaultPointColor;
  const pointSize = this._style.pointSize || defaultPointSize;

  // Batch add points to the collection
  for (let i = 0; i < pointBatches.length; i++) {
    const batch = pointBatches[i];
    if (batch.length === 0) {
      continue;
    }

    for (let j = 0; j < batch.length; j++) {
      const point = batch[j];
      this._pointPrimitiveCollection.add({
        position: point.position,
        color: pointColor,
        pixelSize: pointSize,
      });
    }
  }
};

/**
 * Creates polygon outline primitives from batched geometries (for non-ground outlines).
 * @private
 */
MVTPrimitive.prototype._createPolygonOutlinePrimitives = function () {
  const outlineBatches = this._geometryBatches.polygonOutlines;
  if (!outlineBatches || outlineBatches.length === 0) {
    return;
  }

  for (let i = 0; i < outlineBatches.length; i++) {
    const batch = outlineBatches[i];
    if (batch.length === 0) {
      continue;
    }

    const styleOutlineColor = this._style.outlineColor || defaultOutlineColor;
    const styleOutlineWidth = this._style.outlineWidth || defaultOutlineWidth;

    const primitive = new Primitive({
      geometryInstances: batch,
      appearance: new PerInstanceColorAppearance({
        flat: true,
        translucent: styleOutlineColor.alpha < 1.0,
        renderState: {
          lineWidth: styleOutlineWidth,
        },
      }),
      asynchronous: false,
    });

    primitive.show = this._show;
    this._primitives.push(primitive);
  }
};

/**
 * Processes a single MVT layer and creates geometry instances.
 * @private
 * @param {Object} layer The MVT layer to process.
 * @param {Object} styleOptions Style options to apply.
 */
MVTPrimitive.prototype._processLayer = function (layer, styleOptions) {
  const featuresLength = layer.length;
  for (let i = 0; i < featuresLength; i++) {
    const feature = layer.feature(i);
    if (feature) {
      this._processFeature(feature, layer, styleOptions);
    }
  }
};

/**
 * Processes a single MVT feature and creates appropriate geometry.
 * @private
 * @param {Object} feature The MVT feature to process.
 * @param {Object} layer The parent MVT layer.
 * @param {Object} styleOptions Style options to apply.
 */
MVTPrimitive.prototype._processFeature = function (
  feature,
  layer,
  styleOptions,
) {
  const type = feature.type; // 1 = Point, 2 = LineString, 3 = Polygon

  // Handle different geometry types
  switch (type) {
    case 1: // Point
      this._createPointFeature(feature, styleOptions); // Changed to new method
      break;
    case 2: // LineString
      this._createLineStringGeometry(feature, styleOptions);
      break;
    case 3: // Polygon
      this._createPolygonGeometry(feature, styleOptions);
      break;
    default:
      console.warn("MVTPrimitive: Unknown feature type:", type);
  }
};

/**
 * Creates point geometry for an MVT point feature.
 * Decides whether to use PointPrimitiveCollection (for clamped points) or batch for Primitive (for non-clamped).
 * @private
 * @param {Object} feature The MVT point feature.
 * @param {Object} styleOptions Style options to apply.
 */
MVTPrimitive.prototype._createPointFeature = function (feature, styleOptions) {
  const geometry = feature.loadGeometry();

  for (let i = 0; i < geometry.length; i++) {
    const point = geometry[i][0];
    if (!defined(point)) {
      continue;
    }

    const heightOffset = styleOptions.pointStyle === "billboard" ? 15.0 : 0.0;

    const position = this._tileCoordinatesToCartesian(
      point.x,
      point.y,
      styleOptions.zoom,
      styleOptions.x,
      styleOptions.y,
      feature.extent || DEFAULT_EXTENT,
      heightOffset,
    );

    if (styleOptions.pointStyle === "billboard") {
      if (
        !defined(this._billboardCollection) ||
        this._billboardCollection.isDestroyed()
      ) {
        const scene = defined(this._viewer)
          ? defined(this._viewer.scene)
            ? this._viewer.scene
            : this._viewer
          : undefined;

        if (!defined(scene)) {
          throw new DeveloperError(
            "Height reference is not supported without a scene. " +
              "You must provide a viewer or scene in the constructor options.",
          );
        }

        this._billboardCollection = new BillboardCollection({ scene: scene });
        this._primitives.push(this._billboardCollection);
      }

      const billboardImage = defined(this._billboardImage)
        ? this._billboardImage
        : DEFAULT_MAP_POINT_IMAGE;

      this._billboardCollection.add({
        position: position,
        scale: (styleOptions.pointSize || defaultPointSize) / 32.0,
        verticalOrigin: VerticalOrigin.BOTTOM,
        heightReference: HeightReference.CLAMP_TO_GROUND,
        id: feature.id || createGuid(),
        image: billboardImage,
      });
    } else if (styleOptions.clampToGround) {
      if (
        !defined(this._pointPrimitiveCollection) ||
        this._pointPrimitiveCollection.isDestroyed()
      ) {
        this._pointPrimitiveCollection = new PointPrimitiveCollection();
        this._primitives.push(this._pointPrimitiveCollection);
      }

      this._pointPrimitiveCollection.add({
        position: position,
        pixelSize: styleOptions.pointSize || defaultPointSize,
        color: styleOptions.pointColor || defaultPointColor,
        heightReference: HeightReference.CLAMP_TO_GROUND,
        id: feature.id || createGuid(),
      });
    } else {
      const pointGeometry = {
        attributes: {
          position: new GeometryAttribute({
            componentDatatype: ComponentDatatype.DOUBLE,
            componentsPerAttribute: 3,
            values: new Float64Array([position.x, position.y, position.z]),
          }),
        },
        primitiveType: PrimitiveType.POINTS,
        boundingSphere: new BoundingSphere(position, 1.0),
      };

      this._geometryBatches.points.push(pointGeometry);
    }
  }
};

/**
 * Creates line geometry for an MVT linestring feature.
 * @private
 * @param {Object} feature The MVT linestring feature.
 * @param {Object} styleOptions Style options to apply.
 */
MVTPrimitive.prototype._createLineStringGeometry = function (
  feature,
  styleOptions,
) {
  const geometry = feature.loadGeometry();

  for (let i = 0; i < geometry.length; i++) {
    const line = geometry[i];
    if (line.length < 2) {
      continue;
    }

    const positions = [];
    for (let j = 0; j < line.length; j++) {
      const point = line[j];
      // For GroundPolylineGeometry, height must be 0 as it drapes on terrain.
      // For regular polylines (not clamped), height is 0 relative to ellipsoid.
      const heightForPosition = styleOptions.clampToGround ? 0.0 : 0.0;
      const position = this._tileCoordinatesToCartesian(
        point.x,
        point.y,
        styleOptions.zoom,
        styleOptions.x,
        styleOptions.y,
        feature.extent || DEFAULT_EXTENT,
        heightForPosition,
      );
      positions.push(position);
    }

    if (positions.length < 2) {
      continue;
    }

    if (styleOptions.clampToGround) {
      // Create GroundPolylineGeometry for clamped lines
      // Filter out consecutive duplicate points for GroundPolylineGeometry
      const filteredPositions = [positions[0]];
      for (let k = 1; k < positions.length; k++) {
        if (!Cartesian3.equals(positions[k], positions[k - 1])) {
          filteredPositions.push(positions[k]);
        }
      }
      if (filteredPositions.length < 2) {
        continue;
      }

      const groundLineGeometry = new GroundPolylineGeometry({
        positions: filteredPositions,
        width: styleOptions.strokeWidth || defaultStrokeWidth, // Use strokeWidth from style
        loop: false, // MVT LineStrings are typically not looped
      });

      const groundLineInstance = new GeometryInstance({
        geometry: groundLineGeometry,
        attributes: {
          // Color is handled by MaterialAppearance in _createGroundPolylinePrimitives
          color: ColorGeometryInstanceAttribute.fromColor(
            styleOptions.stroke || defaultStroke,
          ),
        },
        id: createGuid(),
      });
      this._addToBatch(groundLineInstance, "groundPolylines");
      this._geometryInstances.push(groundLineInstance);
    } else {
      // Create regular Polyline for non-clamped lines (original logic path)
      const flattenedPositions = new Float64Array(positions.length * 3);
      for (let j = 0; j < positions.length; j++) {
        flattenedPositions[j * 3] = positions[j].x;
        flattenedPositions[j * 3 + 1] = positions[j].y;
        flattenedPositions[j * 3 + 2] = positions[j].z;
      }

      const indices = new Uint16Array((positions.length - 1) * 2);
      for (let j = 0; j < positions.length - 1; j++) {
        indices[j * 2] = j;
        indices[j * 2 + 1] = j + 1;
      }

      const boundingSphere = BoundingSphere.fromPoints(positions);

      const lineGeometry = {
        attributes: {
          position: new GeometryAttribute({
            componentDatatype: ComponentDatatype.DOUBLE,
            componentsPerAttribute: 3,
            values: flattenedPositions,
          }),
        },
        indices: indices,
        primitiveType: PrimitiveType.LINES,
        boundingSphere: boundingSphere,
      };

      const lineInstance = new GeometryInstance({
        geometry: lineGeometry,
        attributes: {
          color: ColorGeometryInstanceAttribute.fromColor(
            styleOptions.stroke || defaultStroke,
          ),
        },
        id: createGuid(),
      });

      this._addToBatch(lineInstance, "regularPolylines");
      this._geometryInstances.push(lineInstance);
    }
  }
};

/**
 * Creates polygon geometry for an MVT polygon feature.
 * @private
 * @param {Object} feature The MVT polygon feature.
 * @param {Object} styleOptions Style options to apply.
 */
MVTPrimitive.prototype._createPolygonGeometry = function (
  feature,
  styleOptions,
) {
  const geometry = feature.loadGeometry(); // Array of rings, first is exterior.
  if (geometry.length === 0) {
    return;
  }

  const exteriorRingRaw = geometry[0]; // Array of MVT points {x, y}
  if (exteriorRingRaw.length < 3) {
    return;
  }

  // Convert exterior ring to Cartesian positions for the polygon fill
  const exteriorPositionsFill = [];
  for (let i = 0; i < exteriorRingRaw.length; i++) {
    const point = exteriorRingRaw[i];
    const position = this._tileCoordinatesToCartesian(
      point.x,
      point.y,
      styleOptions.zoom,
      styleOptions.x,
      styleOptions.y,
      feature.extent || DEFAULT_EXTENT,
      // For fill, if clampToGround (via styleOptions) is true, GroundPrimitive handles actual clamping.
      // If not clampToGround, use POLYGON_HEIGHT_OFFSET.
      styleOptions.clampToGround ? 1.0 : POLYGON_HEIGHT_OFFSET,
    );
    exteriorPositionsFill.push(position);
  }

  const polygonHierarchy = new PolygonHierarchy(exteriorPositionsFill);

  // Create polygon fill geometry instance
  const polygonGeometry = new PolygonGeometry({
    polygonHierarchy: polygonHierarchy,
    perPositionHeight: true,
  });

  const polygonInstance = new GeometryInstance({
    geometry: polygonGeometry,
    attributes: {
      color: ColorGeometryInstanceAttribute.fromColor(styleOptions.fill),
    },
    id: createGuid(),
  });

  this._addToBatch(polygonInstance, "polygons");
  this._geometryInstances.push(polygonInstance);

  // Create polygon outline if enabled
  if (styleOptions.outline) {
    if (this._clampToGround) {
      // If the entire MVTPrimitive is clamped to ground
      const groundLinePositions = [];
      let lastPosition; // Keep track of the last added position (lint fix: removed explicit undefined)
      for (let i = 0; i < exteriorRingRaw.length; i++) {
        // Use original, non-closed ring
        const point = exteriorRingRaw[i];
        const position = this._tileCoordinatesToCartesian(
          point.x,
          point.y,
          styleOptions.zoom,
          styleOptions.x,
          styleOptions.y,
          feature.extent || DEFAULT_EXTENT,
          0.0, // Height must be 0 for GroundPolylineGeometry positions
        );

        // Add position only if it's different from the last one to avoid zero-length segments
        if (
          !defined(lastPosition) ||
          !Cartesian3.equals(position, lastPosition)
        ) {
          groundLinePositions.push(position);
          lastPosition = position;
        }
      }

      // If, after filtering, the first and last points are the same, remove the last one
      // because GroundPolylineGeometry with loop=true will close it.
      if (
        groundLinePositions.length > 1 &&
        Cartesian3.equals(
          groundLinePositions[0],
          groundLinePositions[groundLinePositions.length - 1],
        )
      ) {
        groundLinePositions.pop();
      }

      if (groundLinePositions.length >= 2) {
        const groundOutlineGeometry = new GroundPolylineGeometry({
          positions: groundLinePositions, // Pass the filtered, open ring
          width: styleOptions.outlineWidth, // Pixel width for GroundPolylineGeometry
          loop: true, // GroundPolylineGeometry will close the loop
        });

        const groundPolygonOutlineInstance = new GeometryInstance({
          geometry: groundOutlineGeometry,
          attributes: {
            // This color attribute will be effectively ignored by MaterialAppearance on GroundPolylinePrimitive
            // but we set it for consistency or if the appearance strategy changes later.
            color: ColorGeometryInstanceAttribute.fromColor(
              styleOptions.outlineColor,
            ),
          },
          id: createGuid(),
        });
        this._addToBatch(groundPolygonOutlineInstance, "groundPolylines"); // Add to groundPolylines batch
        this._geometryInstances.push(groundPolygonOutlineInstance);
      }
    } else {
      // Not clamping to ground for the MVTPrimitive
      // Use PolygonOutlineGeometry.
      // The polygonHierarchy is already based on exteriorPositionsFill,
      // which are at POLYGON_HEIGHT_OFFSET if not clamped.
      const outlineGeometry = new PolygonOutlineGeometry({
        polygonHierarchy: polygonHierarchy,
      });

      const polygonOutlineInstance = new GeometryInstance({
        geometry: outlineGeometry,
        attributes: {
          color: ColorGeometryInstanceAttribute.fromColor(
            styleOptions.outlineColor,
          ),
        },
        id: createGuid(),
      });
      // Add to 'polygonOutlines' batch for non-ground rendering
      this._addToBatch(polygonOutlineInstance, "polygonOutlines");
      this._geometryInstances.push(polygonOutlineInstance);
    }
  }
};

/**
 * Adds a geometry instance to the appropriate batch.
 * @private
 * @param {GeometryInstance} instance The geometry instance.
 * @param {String} type The geometry type: 'polygons', 'polylines', or 'points'.
 */
MVTPrimitive.prototype._addToBatch = function (instance, type) {
  if (!this._geometryBatches[type]) {
    return;
  }

  // Add to an existing batch if it has room, or create a new batch
  let batch =
    this._geometryBatches[type][this._geometryBatches[type].length - 1];

  if (!batch || batch.length >= MAXIMUM_BATCH_SIZE) {
    batch = [];
    this._geometryBatches[type].push(batch);
  }

  batch.push(instance);
};

/**
 * Converts MVT tile local coordinates to global Cartesian coordinates.
 * @private
 * @param {Number} x The x coordinate in tile local space.
 * @param {Number} y The y coordinate in tile local space.
 * @param {Number} zoom The zoom level.
 * @param {Number} tileX The tile x index.
 * @param {Number} tileY The tile y index.
 * @param {Number} extent The MVT extent.
 * @param {Number} [height=0] The height value to use for the coordinate.
 * @returns {Cartesian3} The global Cartesian coordinate.
 */
MVTPrimitive.prototype._tileCoordinatesToCartesian = function (
  x,
  y,
  zoom,
  tileX,
  tileY,
  extent,
  height,
) {
  // Get the tile's rectangle based on the tiling scheme (WebMercator or Geographic)
  const tilingScheme = this._tilingScheme;
  const rectangle = tilingScheme.tileXYToRectangle(tileX, tileY, zoom);

  // Scale pixel coordinates to [0,1] range
  const xFrac = x / extent;
  const yFrac = y / extent;

  // Calculate longitude and latitude
  // Note: MVT uses the convention where y=0 is at the top of the tile,
  // so we need to invert the y fraction (1-yFrac)
  const longitude = rectangle.west + xFrac * (rectangle.east - rectangle.west);
  const latitude =
    rectangle.north - yFrac * (rectangle.north - rectangle.south);

  // Convert to Cartesian with specified height
  return Cartesian3.fromRadians(longitude, latitude, height || 0);
};

/**
 * Decodes MVT data from a binary buffer.
 * @private
 * @param {ArrayBuffer} arrayBuffer The MVT binary data.
 * @returns {Object} Decoded vector tile.
 */
MVTPrimitive.prototype._decodeMVT = function (arrayBuffer) {
  try {
    const pbf = new Pbf(new Uint8Array(arrayBuffer));
    return new VectorTile(pbf);
  } catch (error) {
    throw new RuntimeError(`Failed to parse MVT data: ${error.message}`);
  }
};

/**
 * Called by Scene to update the primitive.
 * @param {FrameState} frameState The current frame state.
 */
MVTPrimitive.prototype.update = function (frameState) {
  if (!this._show) {
    return;
  }

  // Update underlying primitives
  for (let i = 0; i < this._primitives.length; i++) {
    this._primitives[i].update(frameState);
  }
};

/**
 * Returns true if this object was destroyed; otherwise, false.
 * @returns {Boolean} If this object was destroyed.
 */
MVTPrimitive.prototype.isDestroyed = function () {
  return false;
};

/**
 * Destroys the WebGL resources held by this object.
 */
MVTPrimitive.prototype.destroy = function () {
  this._clearExistingPrimitives();
  return destroyObject(this);
};

/**
 * Creates a new MVTPrimitive instance and loads data from the given URL.
 * @param {String|Resource} url The URL to load MVT data from.
 * @param {MVTPrimitive.StyleOptions} options Style options for the MVT features.
 * @returns {Promise<MVTPrimitive>} A promise that resolves to the created MVTPrimitive instance.
 */
MVTPrimitive.load = function (url, options) {
  const mvtPrimitive = new MVTPrimitive(options);
  return mvtPrimitive.load(url, options);
};

export default MVTPrimitive;
